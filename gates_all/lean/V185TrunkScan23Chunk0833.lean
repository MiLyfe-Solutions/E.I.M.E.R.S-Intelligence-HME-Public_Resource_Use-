import V185TrunkScan23Chunk0832

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4929105 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_4929105 : Nat := 118140960795 + 4929105 * 2 ^ 59
def prefixEnd_4929105 : Nat := 4983230072969 + 3 ^ 40 * 4929105 * 2
def baseEnd_4929105 : Nat := 2531000061480042587718965

theorem tailTrace_4929105 : CollatzResearch.WordTrace tailWord_4929105 prefixEnd_4929105 2531000061480042587718965 := by
  unfold tailWord_4929105
  simp only [CollatzResearch.WordTrace]
  refine ⟨179779228807701883958068769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119852819205134589305379179 179779228807701883958068769)
  ·
    refine ⟨134834421605776412968551577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179779228807701883958068769 134834421605776412968551577)
    ·
      refine ⟨101125816204332309726413683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134834421605776412968551577 101125816204332309726413683)
      ·
        refine ⟨151688724306498464589620525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101125816204332309726413683 151688724306498464589620525)
        ·
          refine ⟨56883271614936924221107697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151688724306498464589620525 56883271614936924221107697)
          ·
            refine ⟨42662453711202693165830773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56883271614936924221107697 42662453711202693165830773)
            ·
              refine ⟨3999605035425252484296635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42662453711202693165830773 3999605035425252484296635)
              ·
                refine ⟨5999407553137878726444953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999605035425252484296635 5999407553137878726444953)
                ·
                  refine ⟨4499555664853409044833715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999407553137878726444953 4499555664853409044833715)
                  ·
                    refine ⟨6749333497280113567250573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4499555664853409044833715 6749333497280113567250573)
                    ·
                      refine ⟨2531000061480042587718965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6749333497280113567250573 2531000061480042587718965)
                      ·
                        rfl

theorem cell23_4929105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_4929105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929105 prefixEnd_4929105 := by exact prefixLift 4929105
  have htrace : WordTrace (prefixWord ++ tailWord_4929105) baseStart_4929105 baseEnd_4929105 := by
    simpa [prefixWord, tailWord_4929105, baseEnd_4929105] using wordTrace_append hprefix tailTrace_4929105
  have hstable : (prefixWord ++ tailWord_4929105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929105).length < 2 ^ (prefixWord ++ tailWord_4929105).sum := by decide
  have hdescent : baseEnd_4929105 < baseStart_4929105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929114 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4929114 : Nat := 118140960795 + 4929114 * 2 ^ 59
def prefixEnd_4929114 : Nat := 4983230072969 + 3 ^ 40 * 4929114 * 2
def baseEnd_4929114 : Nat := 2531004682805933052506423

theorem tailTrace_4929114 : CollatzResearch.WordTrace tailWord_4929114 prefixEnd_4929114 2531004682805933052506423 := by
  unfold tailWord_4929114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44944889266167319623786599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119853038043112852330097597 44944889266167319623786599)
  ·
    refine ⟨67417333899250979435679899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44944889266167319623786599 67417333899250979435679899)
    ·
      refine ⟨101126000848876469153519849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67417333899250979435679899 101126000848876469153519849)
      ·
        refine ⟨75844500636657351865139887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101126000848876469153519849 75844500636657351865139887)
        ·
          refine ⟨113766750954986027797709831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75844500636657351865139887 113766750954986027797709831)
          ·
            refine ⟨170650126432479041696564747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113766750954986027797709831 170650126432479041696564747)
            ·
              refine ⟨255975189648718562544847121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170650126432479041696564747 255975189648718562544847121)
              ·
                refine ⟨191981392236538921908635341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255975189648718562544847121 191981392236538921908635341)
                ·
                  refine ⟨71993022088702095715738253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191981392236538921908635341 71993022088702095715738253)
                  ·
                    refine ⟨26997383283263285893401845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71993022088702095715738253 26997383283263285893401845)
                    ·
                      refine ⟨2531004682805933052506423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26997383283263285893401845 2531004682805933052506423)
                      ·
                        rfl

theorem cell23_4929114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4929114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929114 prefixEnd_4929114 := by exact prefixLift 4929114
  have htrace : WordTrace (prefixWord ++ tailWord_4929114) baseStart_4929114 baseEnd_4929114 := by
    simpa [prefixWord, tailWord_4929114, baseEnd_4929114] using wordTrace_append hprefix tailTrace_4929114
  have hstable : (prefixWord ++ tailWord_4929114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929114).length < 2 ^ (prefixWord ++ tailWord_4929114).sum := by decide
  have hdescent : baseEnd_4929114 < baseStart_4929114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929145 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 2, 2, 2]
def baseStart_4929145 : Nat := 118140960795 + 4929145 * 2 ^ 59
def prefixEnd_4929145 : Nat := 4983230072969 + 3 ^ 40 * 4929145 * 2
def baseEnd_4929145 : Nat := 2531020600706222431218781

theorem tailTrace_4929145 : CollatzResearch.WordTrace tailWord_4929145 prefixEnd_4929145 2531020600706222431218781 := by
  unfold tailWord_4929145
  simp only [CollatzResearch.WordTrace]
  refine ⟨179780687727556970789524889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119853791818371313859683259 179780687727556970789524889)
  ·
    refine ⟨134835515795667728092143667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179780687727556970789524889 134835515795667728092143667)
    ·
      refine ⟨202253273693501592138215501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134835515795667728092143667 202253273693501592138215501)
      ·
        refine ⟨75844977635063097051830813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202253273693501592138215501 75844977635063097051830813)
        ·
          refine ⟨28441866613148661394436555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75844977635063097051830813 28441866613148661394436555)
          ·
            refine ⟨42662799919722992091654833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28441866613148661394436555 42662799919722992091654833)
            ·
              refine ⟨31997099939792244068741125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42662799919722992091654833 31997099939792244068741125)
              ·
                refine ⟨5999456238711045762888961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31997099939792244068741125 5999456238711045762888961)
                ·
                  refine ⟨4499592179033284322166721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999456238711045762888961 4499592179033284322166721)
                  ·
                    refine ⟨3374694134274963241625041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4499592179033284322166721 3374694134274963241625041)
                    ·
                      refine ⟨2531020600706222431218781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374694134274963241625041 2531020600706222431218781)
                      ·
                        rfl

theorem cell23_4929145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_4929145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929145 prefixEnd_4929145 := by exact prefixLift 4929145
  have htrace : WordTrace (prefixWord ++ tailWord_4929145) baseStart_4929145 baseEnd_4929145 := by
    simpa [prefixWord, tailWord_4929145, baseEnd_4929145] using wordTrace_append hprefix tailTrace_4929145
  have hstable : (prefixWord ++ tailWord_4929145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929145).length < 2 ^ (prefixWord ++ tailWord_4929145).sum := by decide
  have hdescent : baseEnd_4929145 < baseStart_4929145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929161 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_4929161 : Nat := 118140960795 + 4929161 * 2 ^ 59
def prefixEnd_4929161 : Nat := 4983230072969 + 3 ^ 40 * 4929161 * 2
def baseEnd_4929161 : Nat := 2531028816396694368618707

theorem tailTrace_4929161 : CollatzResearch.WordTrace tailWord_4929161 prefixEnd_4929161 2531028816396694368618707 := by
  unfold tailWord_4929161
  simp only [CollatzResearch.WordTrace]
  refine ⟨179781271295499005522107337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119854180863666003681404891 179781271295499005522107337)
  ·
    refine ⟨134835953471624254141580503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179781271295499005522107337 134835953471624254141580503)
    ·
      refine ⟨202253930207436381212370755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134835953471624254141580503 202253930207436381212370755)
      ·
        refine ⟨303380895311154571818556133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202253930207436381212370755 303380895311154571818556133)
        ·
          refine ⟨56883917870841482215979275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303380895311154571818556133 56883917870841482215979275)
          ·
            refine ⟨85325876806262223323968913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56883917870841482215979275 85325876806262223323968913)
            ·
              refine ⟨63994407604696667492976685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85325876806262223323968913 63994407604696667492976685)
              ·
                refine ⟨23997902851761250309866257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63994407604696667492976685 23997902851761250309866257)
                ·
                  refine ⟨17998427138820937732399693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23997902851761250309866257 17998427138820937732399693)
                  ·
                    refine ⟨6749410177057851649649885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17998427138820937732399693 6749410177057851649649885)
                    ·
                      refine ⟨2531028816396694368618707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6749410177057851649649885 2531028816396694368618707)
                      ·
                        rfl

theorem cell23_4929161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_4929161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929161 prefixEnd_4929161 := by exact prefixLift 4929161
  have htrace : WordTrace (prefixWord ++ tailWord_4929161) baseStart_4929161 baseEnd_4929161 := by
    simpa [prefixWord, tailWord_4929161, baseEnd_4929161] using wordTrace_append hprefix tailTrace_4929161
  have hstable : (prefixWord ++ tailWord_4929161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929161).length < 2 ^ (prefixWord ++ tailWord_4929161).sum := by decide
  have hdescent : baseEnd_4929161 < baseStart_4929161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929162 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_4929162 : Nat := 118140960795 + 4929162 * 2 ^ 59
def prefixEnd_4929162 : Nat := 4983230072969 + 3 ^ 40 * 4929162 * 2
def baseEnd_4929162 : Nat := 2531029329877348864706203

theorem tailTrace_4929162 : CollatzResearch.WordTrace tailWord_4929162 prefixEnd_4929162 2531029329877348864706203 := by
  unfold tailWord_4929162
  simp only [CollatzResearch.WordTrace]
  refine ⟨44945326942123845673223435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119854205178996921795262493 44945326942123845673223435)
  ·
    refine ⟨67417990413185768509835153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44945326942123845673223435 67417990413185768509835153)
    ·
      refine ⟨50563492809889326382376365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67417990413185768509835153 50563492809889326382376365)
      ·
        refine ⟨18961309803708497393391137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50563492809889326382376365 18961309803708497393391137)
        ·
          refine ⟨14220982352781373045043353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18961309803708497393391137 14220982352781373045043353)
          ·
            refine ⟨10665736764586029783782515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14220982352781373045043353 10665736764586029783782515)
            ·
              refine ⟨15998605146879044675673773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10665736764586029783782515 15998605146879044675673773)
              ·
                refine ⟨5999476930079641753377665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15998605146879044675673773 5999476930079641753377665)
                ·
                  refine ⟨4499607697559731315033249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999476930079641753377665 4499607697559731315033249)
                  ·
                    refine ⟨3374705773169798486274937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4499607697559731315033249 3374705773169798486274937)
                    ·
                      refine ⟨2531029329877348864706203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374705773169798486274937 2531029329877348864706203)
                      ·
                        rfl

theorem cell23_4929162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_4929162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929162 prefixEnd_4929162 := by exact prefixLift 4929162
  have htrace : WordTrace (prefixWord ++ tailWord_4929162) baseStart_4929162 baseEnd_4929162 := by
    simpa [prefixWord, tailWord_4929162, baseEnd_4929162] using wordTrace_append hprefix tailTrace_4929162
  have hstable : (prefixWord ++ tailWord_4929162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929162).length < 2 ^ (prefixWord ++ tailWord_4929162).sum := by decide
  have hdescent : baseEnd_4929162 < baseStart_4929162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929211 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 7, 4]
def baseStart_4929211 : Nat := 118140960795 + 4929211 * 2 ^ 59
def prefixEnd_4929211 : Nat := 4983230072969 + 3 ^ 40 * 4929211 * 2
def baseEnd_4929211 : Nat := 843684830143139724331159

theorem tailTrace_4929211 : CollatzResearch.WordTrace tailWord_4929211 prefixEnd_4929211 843684830143139724331159 := by
  unfold tailWord_4929211
  simp only [CollatzResearch.WordTrace]
  refine ⟨179783094945317864061427487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119855396630211909374284991 179783094945317864061427487)
  ·
    refine ⟨269674642417976796092141231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179783094945317864061427487 269674642417976796092141231)
    ·
      refine ⟨404511963626965194138211847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269674642417976796092141231 404511963626965194138211847)
      ·
        refine ⟨606767945440447791207317771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404511963626965194138211847 606767945440447791207317771)
        ·
          refine ⟨910151918160671686810976657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606767945440447791207317771 910151918160671686810976657)
          ·
            refine ⟨682613938620503765108232493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910151918160671686810976657 682613938620503765108232493)
            ·
              refine ⟨255980226982688911915587185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682613938620503765108232493 255980226982688911915587185)
              ·
                refine ⟨191985170237016683936690389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255980226982688911915587185 191985170237016683936690389)
                ·
                  refine ⟨4499652427430078529766181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 191985170237016683936690389 4499652427430078529766181)
                  ·
                    refine ⟨843684830143139724331159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499652427430078529766181 843684830143139724331159)
                    ·
                      rfl

theorem cell23_4929211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 4].length) (baseStart_4929211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929211 prefixEnd_4929211 := by exact prefixLift 4929211
  have htrace : WordTrace (prefixWord ++ tailWord_4929211) baseStart_4929211 baseEnd_4929211 := by
    simpa [prefixWord, tailWord_4929211, baseEnd_4929211] using wordTrace_append hprefix tailTrace_4929211
  have hstable : (prefixWord ++ tailWord_4929211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929211).length < 2 ^ (prefixWord ++ tailWord_4929211).sum := by decide
  have hdescent : baseEnd_4929211 < baseStart_4929211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929221 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_4929221 : Nat := 118140960795 + 4929221 * 2 ^ 59
def prefixEnd_4929221 : Nat := 4983230072969 + 3 ^ 40 * 4929221 * 2
def baseEnd_4929221 : Nat := 2531059625235964133868431

theorem tailTrace_4929221 : CollatzResearch.WordTrace tailWord_4929221 prefixEnd_4929221 2531059625235964133868431 := by
  unfold tailWord_4929221
  simp only [CollatzResearch.WordTrace]
  refine ⟨179783459675281635769291517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119855639783521090512861011 179783459675281635769291517)
  ·
    refine ⟨67418797378230613413484319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179783459675281635769291517 67418797378230613413484319)
    ·
      refine ⟨101128196067345920120226479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67418797378230613413484319 101128196067345920120226479)
      ·
        refine ⟨151692294101018880180339719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101128196067345920120226479 151692294101018880180339719)
        ·
          refine ⟨227538441151528320270509579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151692294101018880180339719 227538441151528320270509579)
          ·
            refine ⟨341307661727292480405764369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227538441151528320270509579 341307661727292480405764369)
            ·
              refine ⟨255980746295469360304323277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341307661727292480405764369 255980746295469360304323277)
              ·
                refine ⟨95992779860801010114121229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255980746295469360304323277 95992779860801010114121229)
                ·
                  refine ⟨35997292447800378792795461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95992779860801010114121229 35997292447800378792795461)
                  ·
                    refine ⟨6749492333962571023649149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35997292447800378792795461 6749492333962571023649149)
                    ·
                      refine ⟨2531059625235964133868431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6749492333962571023649149 2531059625235964133868431)
                      ·
                        rfl

theorem cell23_4929221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_4929221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929221 prefixEnd_4929221 := by exact prefixLift 4929221
  have htrace : WordTrace (prefixWord ++ tailWord_4929221) baseStart_4929221 baseEnd_4929221 := by
    simpa [prefixWord, tailWord_4929221, baseEnd_4929221] using wordTrace_append hprefix tailTrace_4929221
  have hstable : (prefixWord ++ tailWord_4929221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929221).length < 2 ^ (prefixWord ++ tailWord_4929221).sum := by decide
  have hdescent : baseEnd_4929221 < baseStart_4929221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929258 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_4929258 : Nat := 118140960795 + 4929258 * 2 ^ 59
def prefixEnd_4929258 : Nat := 4983230072969 + 3 ^ 40 * 4929258 * 2
def baseEnd_4929258 : Nat := 281230958224464498789529

theorem tailTrace_4929258 : CollatzResearch.WordTrace tailWord_4929258 prefixEnd_4929258 281230958224464498789529 := by
  unfold tailWord_4929258
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946202294036897772097107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119856539450765060725592285 44946202294036897772097107)
  ·
    refine ⟨67419303441055346658145661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44946202294036897772097107 67419303441055346658145661)
    ·
      refine ⟨25282238790395754996804623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67419303441055346658145661 25282238790395754996804623)
      ·
        refine ⟨37923358185593632495206935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25282238790395754996804623 37923358185593632495206935)
        ·
          refine ⟨56885037278390448742810403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37923358185593632495206935 56885037278390448742810403)
          ·
            refine ⟨85327555917585673114215605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56885037278390448742810403 85327555917585673114215605)
            ·
              refine ⟨7999458367273656854457713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85327555917585673114215605 7999458367273656854457713)
              ·
                refine ⟨5999593775455242640843285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7999458367273656854457713 5999593775455242640843285)
                ·
                  refine ⟨281230958224464498789529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5999593775455242640843285 281230958224464498789529)
                  ·
                    rfl

theorem cell23_4929258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_4929258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929258 prefixEnd_4929258 := by exact prefixLift 4929258
  have htrace : WordTrace (prefixWord ++ tailWord_4929258) baseStart_4929258 baseEnd_4929258 := by
    simpa [prefixWord, tailWord_4929258, baseEnd_4929258] using wordTrace_append hprefix tailTrace_4929258
  have hstable : (prefixWord ++ tailWord_4929258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929258).length < 2 ^ (prefixWord ++ tailWord_4929258).sum := by decide
  have hdescent : baseEnd_4929258 < baseStart_4929258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929271 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 5, 5]
def baseStart_4929271 : Nat := 118140960795 + 4929271 * 2 ^ 59
def prefixEnd_4929271 : Nat := 4983230072969 + 3 ^ 40 * 4929271 * 2
def baseEnd_4929271 : Nat := 843695099756229646081067

theorem tailTrace_4929271 : CollatzResearch.WordTrace tailWord_4929271 prefixEnd_4929271 843695099756229646081067 := by
  unfold tailWord_4929271
  simp only [CollatzResearch.WordTrace]
  refine ⟨179785283325100494308611667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119856855550066996205741111 179785283325100494308611667)
  ·
    refine ⟨269677924987650741462917501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179785283325100494308611667 269677924987650741462917501)
    ·
      refine ⟨101129221870369028048594063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269677924987650741462917501 101129221870369028048594063)
      ·
        refine ⟨151693832805553542072891095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101129221870369028048594063 151693832805553542072891095)
        ·
          refine ⟨227540749208330313109336643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151693832805553542072891095 227540749208330313109336643)
          ·
            refine ⟨341311123812495469664004965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227540749208330313109336643 341311123812495469664004965)
            ·
              refine ⟨63995835714842900562000931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341311123812495469664004965 63995835714842900562000931)
              ·
                refine ⟨95993753572264350843001397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63995835714842900562000931 95993753572264350843001397)
                ·
                  refine ⟨8999414397399782891531381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95993753572264350843001397 8999414397399782891531381)
                  ·
                    refine ⟨843695099756229646081067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8999414397399782891531381 843695099756229646081067)
                    ·
                      rfl

theorem cell23_4929271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_4929271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929271 prefixEnd_4929271 := by exact prefixLift 4929271
  have htrace : WordTrace (prefixWord ++ tailWord_4929271) baseStart_4929271 baseEnd_4929271 := by
    simpa [prefixWord, tailWord_4929271, baseEnd_4929271] using wordTrace_append hprefix tailTrace_4929271
  have hstable : (prefixWord ++ tailWord_4929271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929271).length < 2 ^ (prefixWord ++ tailWord_4929271).sum := by decide
  have hdescent : baseEnd_4929271 < baseStart_4929271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929281 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4929281 : Nat := 118140960795 + 4929281 * 2 ^ 59
def prefixEnd_4929281 : Nat := 4983230072969 + 3 ^ 40 * 4929281 * 2
def baseEnd_4929281 : Nat := 2531090434075233899118155

theorem tailTrace_4929281 : CollatzResearch.WordTrace tailWord_4929281 prefixEnd_4929281 2531090434075233899118155 := by
  unfold tailWord_4929281
  simp only [CollatzResearch.WordTrace]
  refine ⟨179785648055064266016475697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119857098703376177344317131 179785648055064266016475697)
  ·
    refine ⟨134839236041298199512356773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179785648055064266016475697 134839236041298199512356773)
    ·
      refine ⟨25282356757743412408566895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134839236041298199512356773 25282356757743412408566895)
      ·
        refine ⟨37923535136615118612850343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25282356757743412408566895 37923535136615118612850343)
        ·
          refine ⟨56885302704922677919275515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37923535136615118612850343 56885302704922677919275515)
          ·
            refine ⟨85327954057384016878913273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56885302704922677919275515 85327954057384016878913273)
            ·
              refine ⟨63995965543038012659184955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85327954057384016878913273 63995965543038012659184955)
              ·
                refine ⟨95993948314557018988777433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63995965543038012659184955 95993948314557018988777433)
                ·
                  refine ⟨71995461235917764241583075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95993948314557018988777433 71995461235917764241583075)
                  ·
                    refine ⟨107993191853876646362374613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71995461235917764241583075 107993191853876646362374613)
                    ·
                      refine ⟨2531090434075233899118155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107993191853876646362374613 2531090434075233899118155)
                      ·
                        rfl

theorem cell23_4929281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4929281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929281 prefixEnd_4929281 := by exact prefixLift 4929281
  have htrace : WordTrace (prefixWord ++ tailWord_4929281) baseStart_4929281 baseEnd_4929281 := by
    simpa [prefixWord, tailWord_4929281, baseEnd_4929281] using wordTrace_append hprefix tailTrace_4929281
  have hstable : (prefixWord ++ tailWord_4929281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929281).length < 2 ^ (prefixWord ++ tailWord_4929281).sum := by decide
  have hdescent : baseEnd_4929281 < baseStart_4929281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929321 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_4929321 : Nat := 118140960795 + 4929321 * 2 ^ 59
def prefixEnd_4929321 : Nat := 4983230072969 + 3 ^ 40 * 4929321 * 2
def baseEnd_4929321 : Nat := 2531110973301413742617971

theorem tailTrace_4929321 : CollatzResearch.WordTrace tailWord_4929321 prefixEnd_4929321 2531110973301413742617971 := by
  unfold tailWord_4929321
  simp only [CollatzResearch.WordTrace]
  refine ⟨179787106974919352847931817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119858071316612901898621211 179787106974919352847931817)
  ·
    refine ⟨134840330231189514635948863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179787106974919352847931817 134840330231189514635948863)
    ·
      refine ⟨202260495346784271953923295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134840330231189514635948863 202260495346784271953923295)
      ·
        refine ⟨303390743020176407930884943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202260495346784271953923295 303390743020176407930884943)
        ·
          refine ⟨455086114530264611896327415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303390743020176407930884943 455086114530264611896327415)
          ·
            refine ⟨682629171795396917844491123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455086114530264611896327415 682629171795396917844491123)
            ·
              refine ⟨1023943757693095376766736685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682629171795396917844491123 1023943757693095376766736685)
              ·
                refine ⟨383978909134910766287526257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023943757693095376766736685 383978909134910766287526257)
                ·
                  refine ⟨287984181851183074715644693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383978909134910766287526257 287984181851183074715644693)
                  ·
                    refine ⟨13499258524274206627295845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 287984181851183074715644693 13499258524274206627295845)
                    ·
                      refine ⟨2531110973301413742617971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13499258524274206627295845 2531110973301413742617971)
                      ·
                        rfl

theorem cell23_4929321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_4929321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929321 prefixEnd_4929321 := by exact prefixLift 4929321
  have htrace : WordTrace (prefixWord ++ tailWord_4929321) baseStart_4929321 baseEnd_4929321 := by
    simpa [prefixWord, tailWord_4929321, baseEnd_4929321] using wordTrace_append hprefix tailTrace_4929321
  have hstable : (prefixWord ++ tailWord_4929321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929321).length < 2 ^ (prefixWord ++ tailWord_4929321).sum := by decide
  have hdescent : baseEnd_4929321 < baseStart_4929321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929338 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_4929338 : Nat := 118140960795 + 4929338 * 2 ^ 59
def prefixEnd_4929338 : Nat := 4983230072969 + 3 ^ 40 * 4929338 * 2
def baseEnd_4929338 : Nat := 2531119702472540176105393

theorem tailTrace_4929338 : CollatzResearch.WordTrace tailWord_4929338 prefixEnd_4929338 2531119702472540176105393 := by
  unfold tailWord_4929338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44946931753964441187825167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119858484677238509834200445 44946931753964441187825167)
  ·
    refine ⟨67420397630946661781737751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44946931753964441187825167 67420397630946661781737751)
    ·
      refine ⟨101130596446419992672606627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67420397630946661781737751 101130596446419992672606627)
      ·
        refine ⟨151695894669629989008909941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101130596446419992672606627 151695894669629989008909941)
        ·
          refine ⟨14221490125277811469585307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151695894669629989008909941 14221490125277811469585307)
          ·
            refine ⟨21332235187916717204377961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14221490125277811469585307 21332235187916717204377961)
            ·
              refine ⟨15999176390937537903283471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21332235187916717204377961 15999176390937537903283471)
              ·
                refine ⟨23998764586406306854925207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15999176390937537903283471 23998764586406306854925207)
                ·
                  refine ⟨35998146879609460282387811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23998764586406306854925207 35998146879609460282387811)
                  ·
                    refine ⟨53997220319414190423581717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35998146879609460282387811 53997220319414190423581717)
                    ·
                      refine ⟨2531119702472540176105393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53997220319414190423581717 2531119702472540176105393)
                      ·
                        rfl

theorem cell23_4929338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_4929338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929338 prefixEnd_4929338 := by exact prefixLift 4929338
  have htrace : WordTrace (prefixWord ++ tailWord_4929338) baseStart_4929338 baseEnd_4929338 := by
    simpa [prefixWord, tailWord_4929338, baseEnd_4929338] using wordTrace_append hprefix tailTrace_4929338
  have hstable : (prefixWord ++ tailWord_4929338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929338).length < 2 ^ (prefixWord ++ tailWord_4929338).sum := by decide
  have hdescent : baseEnd_4929338 < baseStart_4929338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929342 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4929342 : Nat := 118140960795 + 4929342 * 2 ^ 59
def prefixEnd_4929342 : Nat := 4983230072969 + 3 ^ 40 * 4929342 * 2
def baseEnd_4929342 : Nat := 2531121756395158160455375

theorem tailTrace_4929342 : CollatzResearch.WordTrace tailWord_4929342 prefixEnd_4929342 2531121756395158160455375 := by
  unfold tailWord_4929342
  simp only [CollatzResearch.WordTrace]
  refine ⟨22473484113480409179305785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119858581938562182289630853 22473484113480409179305785)
  ·
    refine ⟨16855113085110306884479339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22473484113480409179305785 16855113085110306884479339)
    ·
      refine ⟨25282669627665460326719009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16855113085110306884479339 25282669627665460326719009)
      ·
        refine ⟨18962002220749095245039257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25282669627665460326719009 18962002220749095245039257)
        ·
          refine ⟨14221501665561821433779443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18962002220749095245039257 14221501665561821433779443)
          ·
            refine ⟨21332252498342732150669165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14221501665561821433779443 21332252498342732150669165)
            ·
              refine ⟨7999594686878524556500937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21332252498342732150669165 7999594686878524556500937)
              ·
                refine ⟨5999696015158893417375703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7999594686878524556500937 5999696015158893417375703)
                ·
                  refine ⟨8999544022738340126063555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999696015158893417375703 8999544022738340126063555)
                  ·
                    refine ⟨13499316034107510189095333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8999544022738340126063555 13499316034107510189095333)
                    ·
                      refine ⟨2531121756395158160455375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13499316034107510189095333 2531121756395158160455375)
                      ·
                        rfl

theorem cell23_4929342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4929342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929342 prefixEnd_4929342 := by exact prefixLift 4929342
  have htrace : WordTrace (prefixWord ++ tailWord_4929342) baseStart_4929342 baseEnd_4929342 := by
    simpa [prefixWord, tailWord_4929342, baseEnd_4929342] using wordTrace_append hprefix tailTrace_4929342
  have hstable : (prefixWord ++ tailWord_4929342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929342).length < 2 ^ (prefixWord ++ tailWord_4929342).sum := by decide
  have hdescent : baseEnd_4929342 < baseStart_4929342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929376 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 1, 2, 2]
def baseStart_4929376 : Nat := 118140960795 + 4929376 * 2 ^ 59
def prefixEnd_4929376 : Nat := 4983230072969 + 3 ^ 40 * 4929376 * 2
def baseEnd_4929376 : Nat := 2531139214737411027430219

theorem tailTrace_4929376 : CollatzResearch.WordTrace tailWord_4929376 prefixEnd_4929376 2531139214737411027430219 := by
  unfold tailWord_4929376
  simp only [CollatzResearch.WordTrace]
  refine ⟨89894556494860048620591991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119859408659813398160789321 89894556494860048620591991)
  ·
    refine ⟨134841834742290072930887987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89894556494860048620591991 134841834742290072930887987)
    ·
      refine ⟨202262752113435109396331981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134841834742290072930887987 202262752113435109396331981)
      ·
        refine ⟨75848532042538166023624493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202262752113435109396331981 75848532042538166023624493)
        ·
          refine ⟨28443199515951812258859185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75848532042538166023624493 28443199515951812258859185)
          ·
            refine ⟨21332399636963859194144389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28443199515951812258859185 21332399636963859194144389)
            ·
              refine ⟨3999824931930723598902073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21332399636963859194144389 3999824931930723598902073)
              ·
                refine ⟨2999868698948042699176555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3999824931930723598902073 2999868698948042699176555)
                ·
                  refine ⟨4499803048422064048764833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999868698948042699176555 4499803048422064048764833)
                  ·
                    refine ⟨3374852286316548036573625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4499803048422064048764833 3374852286316548036573625)
                    ·
                      refine ⟨2531139214737411027430219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374852286316548036573625 2531139214737411027430219)
                      ·
                        rfl

theorem cell23_4929376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_4929376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929376 prefixEnd_4929376 := by exact prefixLift 4929376
  have htrace : WordTrace (prefixWord ++ tailWord_4929376) baseStart_4929376 baseEnd_4929376 := by
    simpa [prefixWord, tailWord_4929376, baseEnd_4929376] using wordTrace_append hprefix tailTrace_4929376
  have hstable : (prefixWord ++ tailWord_4929376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929376).length < 2 ^ (prefixWord ++ tailWord_4929376).sum := by decide
  have hdescent : baseEnd_4929376 < baseStart_4929376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929426 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4929426 : Nat := 118140960795 + 4929426 * 2 ^ 59
def prefixEnd_4929426 : Nat := 4983230072969 + 3 ^ 40 * 4929426 * 2
def baseEnd_4929426 : Nat := 2531164888770135831804989

theorem tailTrace_4929426 : CollatzResearch.WordTrace tailWord_4929426 prefixEnd_4929426 2531164888770135831804989 := by
  unfold tailWord_4929426
  simp only [CollatzResearch.WordTrace]
  refine ⟨44947734159884738945126033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119860624426359303853669421 44947734159884738945126033)
  ·
    refine ⟨33710800619913554208844525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44947734159884738945126033 33710800619913554208844525)
    ·
      refine ⟨12641550232467582828316697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33710800619913554208844525 12641550232467582828316697)
      ·
        refine ⟨9481162674350687121237523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12641550232467582828316697 9481162674350687121237523)
        ·
          refine ⟨14221744011526030681856285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9481162674350687121237523 14221744011526030681856285)
          ·
            refine ⟨5333154004322261505696107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14221744011526030681856285 5333154004322261505696107)
            ·
              refine ⟨7999731006483392258544161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5333154004322261505696107 7999731006483392258544161)
              ·
                refine ⟨5999798254862544193908121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7999731006483392258544161 5999798254862544193908121)
                ·
                  refine ⟨4499848691146908145431091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999798254862544193908121 4499848691146908145431091)
                  ·
                    refine ⟨6749773036720362218146637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4499848691146908145431091 6749773036720362218146637)
                    ·
                      refine ⟨2531164888770135831804989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6749773036720362218146637 2531164888770135831804989)
                      ·
                        rfl

theorem cell23_4929426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4929426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929426 prefixEnd_4929426 := by exact prefixLift 4929426
  have htrace : WordTrace (prefixWord ++ tailWord_4929426) baseStart_4929426 baseEnd_4929426 := by
    simpa [prefixWord, tailWord_4929426, baseEnd_4929426] using wordTrace_append hprefix tailTrace_4929426
  have hstable : (prefixWord ++ tailWord_4929426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929426).length < 2 ^ (prefixWord ++ tailWord_4929426).sum := by decide
  have hdescent : baseEnd_4929426 < baseStart_4929426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929492 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4929492 : Nat := 118140960795 + 4929492 * 2 ^ 59
def prefixEnd_4929492 : Nat := 4983230072969 + 3 ^ 40 * 4929492 * 2
def baseEnd_4929492 : Nat := 2531198778493332573579685

theorem tailTrace_4929492 : CollatzResearch.WordTrace tailWord_4929492 prefixEnd_4929492 2531198778493332573579685 := by
  unfold tailWord_4929492
  simp only [CollatzResearch.WordTrace]
  refine ⟨89896671928649924526203365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119862229238199899368271153 89896671928649924526203365)
  ·
    refine ⟨16855625986621860848663131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89896671928649924526203365 16855625986621860848663131)
    ·
      refine ⟨25283438979932791272994697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16855625986621860848663131 25283438979932791272994697)
      ·
        refine ⟨18962579234949593454746023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25283438979932791272994697 18962579234949593454746023)
        ·
          refine ⟨28443868852424390182119035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18962579234949593454746023 28443868852424390182119035)
          ·
            refine ⟨42665803278636585273178553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28443868852424390182119035 42665803278636585273178553)
            ·
              refine ⟨31999352458977438954883915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42665803278636585273178553 31999352458977438954883915)
              ·
                refine ⟨47999028688466158432325873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31999352458977438954883915 47999028688466158432325873)
                ·
                  refine ⟨35999271516349618824244405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47999028688466158432325873 35999271516349618824244405)
                  ·
                    refine ⟨3374931704657776764772913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35999271516349618824244405 3374931704657776764772913)
                    ·
                      refine ⟨2531198778493332573579685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374931704657776764772913 2531198778493332573579685)
                      ·
                        rfl

theorem cell23_4929492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4929492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929492 prefixEnd_4929492 := by exact prefixLift 4929492
  have htrace : WordTrace (prefixWord ++ tailWord_4929492) baseStart_4929492 baseEnd_4929492 := by
    simpa [prefixWord, tailWord_4929492, baseEnd_4929492] using wordTrace_append hprefix tailTrace_4929492
  have hstable : (prefixWord ++ tailWord_4929492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929492).length < 2 ^ (prefixWord ++ tailWord_4929492).sum := by decide
  have hdescent : baseEnd_4929492 < baseStart_4929492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929500 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4929500 : Nat := 118140960795 + 4929500 * 2 ^ 59
def prefixEnd_4929500 : Nat := 4983230072969 + 3 ^ 40 * 4929500 * 2
def baseEnd_4929500 : Nat := 2531202886338568542279649

theorem tailTrace_4929500 : CollatzResearch.WordTrace tailWord_4929500 prefixEnd_4929500 2531202886338568542279649 := by
  unfold tailWord_4929500
  simp only [CollatzResearch.WordTrace]
  refine ⟨89896817820635433209348977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119862423760847244279131969 89896817820635433209348977)
  ·
    refine ⟨67422613365476574907011733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89896817820635433209348977 67422613365476574907011733)
    ·
      refine ⟨3160435001506714448766175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67422613365476574907011733 3160435001506714448766175)
      ·
        refine ⟨4740652502260071673149263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160435001506714448766175 4740652502260071673149263)
        ·
          refine ⟨7110978753390107509723895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740652502260071673149263 7110978753390107509723895)
          ·
            refine ⟨10666468130085161264585843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7110978753390107509723895 10666468130085161264585843)
            ·
              refine ⟨15999702195127741896878765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10666468130085161264585843 15999702195127741896878765)
              ·
                refine ⟨5999888323172903211329537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15999702195127741896878765 5999888323172903211329537)
                ·
                  refine ⟨4499916242379677408497153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5999888323172903211329537 4499916242379677408497153)
                  ·
                    refine ⟨3374937181784758056372865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4499916242379677408497153 3374937181784758056372865)
                    ·
                      refine ⟨2531202886338568542279649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3374937181784758056372865 2531202886338568542279649)
                      ·
                        rfl

theorem cell23_4929500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4929500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929500 prefixEnd_4929500 := by exact prefixLift 4929500
  have htrace : WordTrace (prefixWord ++ tailWord_4929500) baseStart_4929500 baseEnd_4929500 := by
    simpa [prefixWord, tailWord_4929500, baseEnd_4929500] using wordTrace_append hprefix tailTrace_4929500
  have hstable : (prefixWord ++ tailWord_4929500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929500).length < 2 ^ (prefixWord ++ tailWord_4929500).sum := by decide
  have hdescent : baseEnd_4929500 < baseStart_4929500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929515 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 3, 4]
def baseStart_4929515 : Nat := 118140960795 + 4929515 * 2 ^ 59
def prefixEnd_4929515 : Nat := 4983230072969 + 3 ^ 40 * 4929515 * 2
def baseEnd_4929515 : Nat := 843736862849461994530693

theorem tailTrace_4929515 : CollatzResearch.WordTrace tailWord_4929515 prefixEnd_4929515 843736862849461994530693 := by
  unfold tailWord_4929515
  simp only [CollatzResearch.WordTrace]
  refine ⟨179794182736216523980493999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119862788490811015986995999 179794182736216523980493999)
  ·
    refine ⟨269691274104324785970740999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179794182736216523980493999 269691274104324785970740999)
    ·
      refine ⟨404536911156487178956111499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269691274104324785970740999 404536911156487178956111499)
      ·
        refine ⟨606805366734730768434167249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404536911156487178956111499 606805366734730768434167249)
        ·
          refine ⟨455104025051048076325625437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606805366734730768434167249 455104025051048076325625437)
          ·
            refine ⟨170664009394143028622109539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455104025051048076325625437 170664009394143028622109539)
            ·
              refine ⟨255996014091214542933164309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170664009394143028622109539 255996014091214542933164309)
              ·
                refine ⟨11999813160525681699992077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 255996014091214542933164309 11999813160525681699992077)
                ·
                  refine ⟨4499929935197130637497029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11999813160525681699992077 4499929935197130637497029)
                  ·
                    refine ⟨843736862849461994530693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4499929935197130637497029 843736862849461994530693)
                    ·
                      rfl

theorem cell23_4929515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 4].length) (baseStart_4929515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929515 prefixEnd_4929515 := by exact prefixLift 4929515
  have htrace : WordTrace (prefixWord ++ tailWord_4929515) baseStart_4929515 baseEnd_4929515 := by
    simpa [prefixWord, tailWord_4929515, baseEnd_4929515] using wordTrace_append hprefix tailTrace_4929515
  have hstable : (prefixWord ++ tailWord_4929515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929515).length < 2 ^ (prefixWord ++ tailWord_4929515).sum := by decide
  have hdescent : baseEnd_4929515 < baseStart_4929515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929528 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 10]
def baseStart_4929528 : Nat := 118140960795 + 4929528 * 2 ^ 59
def prefixEnd_4929528 : Nat := 4983230072969 + 3 ^ 40 * 4929528 * 2
def baseEnd_4929528 : Nat := 281246362644099381414391

theorem tailTrace_4929528 : CollatzResearch.WordTrace tailWord_4929528 prefixEnd_4929528 281246362644099381414391 := by
  unfold tailWord_4929528
  simp only [CollatzResearch.WordTrace]
  refine ⟨89897328442584713600358619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119863104590112951467144825 89897328442584713600358619)
  ·
    refine ⟨134845992663877070400537929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89897328442584713600358619 134845992663877070400537929)
    ·
      refine ⟨101134494497907802800403447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134845992663877070400537929 101134494497907802800403447)
      ·
        refine ⟨151701741746861704200605171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101134494497907802800403447 151701741746861704200605171)
        ·
          refine ⟨227552612620292556300907757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151701741746861704200605171 227552612620292556300907757)
          ·
            refine ⟨85332229732609708612840409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227552612620292556300907757 85332229732609708612840409)
            ·
              refine ⟨63999172299457281459630307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85332229732609708612840409 63999172299457281459630307)
              ·
                refine ⟨95998758449185922189445461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63999172299457281459630307 95998758449185922189445461)
                ·
                  refine ⟨281246362644099381414391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95998758449185922189445461 281246362644099381414391)
                  ·
                    rfl

theorem cell23_4929528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_4929528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929528 prefixEnd_4929528 := by exact prefixLift 4929528
  have htrace : WordTrace (prefixWord ++ tailWord_4929528) baseStart_4929528 baseEnd_4929528 := by
    simpa [prefixWord, tailWord_4929528, baseEnd_4929528] using wordTrace_append hprefix tailTrace_4929528
  have hstable : (prefixWord ++ tailWord_4929528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929528).length < 2 ^ (prefixWord ++ tailWord_4929528).sum := by decide
  have hdescent : baseEnd_4929528 < baseStart_4929528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_4929615 : Nat := 118140960795 + 4929615 * 2 ^ 59
def prefixEnd_4929615 : Nat := 4983230072969 + 3 ^ 40 * 4929615 * 2
def baseEnd_4929615 : Nat := 2531261936613835592341619

theorem tailTrace_4929615 : CollatzResearch.WordTrace tailWord_4929615 prefixEnd_4929615 2531261936613835592341619 := by
  unfold tailWord_4929615
  simp only [CollatzResearch.WordTrace]
  refine ⟨179797830035854241059134299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119865220023902827372756199 179797830035854241059134299)
  ·
    refine ⟨269696745053781361588701449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179797830035854241059134299 269696745053781361588701449)
    ·
      refine ⟨202272558790336021191526087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269696745053781361588701449 202272558790336021191526087)
      ·
        refine ⟨303408838185504031787289131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202272558790336021191526087 303408838185504031787289131)
        ·
          refine ⟨455113257278256047680933697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303408838185504031787289131 455113257278256047680933697)
          ·
            refine ⟨341334942958692035760700273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455113257278256047680933697 341334942958692035760700273)
            ·
              refine ⟨256001207219019026820525205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341334942958692035760700273 256001207219019026820525205)
              ·
                refine ⟨12000056588391516882212119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256001207219019026820525205 12000056588391516882212119)
                ·
                  refine ⟨18000084882587275323318179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12000056588391516882212119 18000084882587275323318179)
                  ·
                    refine ⟨27000127323880912984977269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18000084882587275323318179 27000127323880912984977269)
                    ·
                      refine ⟨2531261936613835592341619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27000127323880912984977269 2531261936613835592341619)
                      ·
                        rfl

theorem cell23_4929615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_4929615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929615 prefixEnd_4929615 := by exact prefixLift 4929615
  have htrace : WordTrace (prefixWord ++ tailWord_4929615) baseStart_4929615 baseEnd_4929615 := by
    simpa [prefixWord, tailWord_4929615, baseEnd_4929615] using wordTrace_append hprefix tailTrace_4929615
  have hstable : (prefixWord ++ tailWord_4929615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929615).length < 2 ^ (prefixWord ++ tailWord_4929615).sum := by decide
  have hdescent : baseEnd_4929615 < baseStart_4929615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929625 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_4929625 : Nat := 118140960795 + 4929625 * 2 ^ 59
def prefixEnd_4929625 : Nat := 4983230072969 + 3 ^ 40 * 4929625 * 2
def baseEnd_4929625 : Nat := 2531267071420380553216573

theorem tailTrace_4929625 : CollatzResearch.WordTrace tailWord_4929625 prefixEnd_4929625 2531267071420380553216573 := by
  unfold tailWord_4929625
  simp only [CollatzResearch.WordTrace]
  refine ⟨179798194765818012766998329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119865463177212008511332219 179798194765818012766998329)
  ·
    refine ⟨134848646074363509575248747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179798194765818012766998329 134848646074363509575248747)
    ·
      refine ⟨202272969111545264362873121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134848646074363509575248747 202272969111545264362873121)
      ·
        refine ⟨151704726833658948272154841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202272969111545264362873121 151704726833658948272154841)
        ·
          refine ⟨113778545125244211204116131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151704726833658948272154841 113778545125244211204116131)
          ·
            refine ⟨170667817687866316806174197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113778545125244211204116131 170667817687866316806174197)
            ·
              refine ⟨16000107908237467200578831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170667817687866316806174197 16000107908237467200578831)
              ·
                refine ⟨24000161862356200800868247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16000107908237467200578831 24000161862356200800868247)
                ·
                  refine ⟨36000242793534301201302371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24000161862356200800868247 36000242793534301201302371)
                  ·
                    refine ⟨54000364190301451801953557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36000242793534301201302371 54000364190301451801953557)
                    ·
                      refine ⟨2531267071420380553216573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54000364190301451801953557 2531267071420380553216573)
                      ·
                        rfl

theorem cell23_4929625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_4929625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929625 prefixEnd_4929625 := by exact prefixLift 4929625
  have htrace : WordTrace (prefixWord ++ tailWord_4929625) baseStart_4929625 baseEnd_4929625 := by
    simpa [prefixWord, tailWord_4929625, baseEnd_4929625] using wordTrace_append hprefix tailTrace_4929625
  have hstable : (prefixWord ++ tailWord_4929625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929625).length < 2 ^ (prefixWord ++ tailWord_4929625).sum := by decide
  have hdescent : baseEnd_4929625 < baseStart_4929625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929713 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4929713 : Nat := 118140960795 + 4929713 * 2 ^ 59
def prefixEnd_4929713 : Nat := 4983230072969 + 3 ^ 40 * 4929713 * 2
def baseEnd_4929713 : Nat := 2531312257717976208916169

theorem tailTrace_4929713 : CollatzResearch.WordTrace tailWord_4929713 prefixEnd_4929713 2531312257717976208916169 := by
  unfold tailWord_4929713
  simp only [CollatzResearch.WordTrace]
  refine ⟨179801404389499203796201793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119867602926332802530801195 179801404389499203796201793)
  ·
    refine ⟨134851053292124402847151345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179801404389499203796201793 134851053292124402847151345)
    ·
      refine ⟨101138289969093302135363509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134851053292124402847151345 101138289969093302135363509)
      ·
        refine ⟨9481714684602497075190329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101138289969093302135363509 9481714684602497075190329)
        ·
          refine ⟨7111286013451872806392747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9481714684602497075190329 7111286013451872806392747)
          ·
            refine ⟨10666929020177809209589121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111286013451872806392747 10666929020177809209589121)
            ·
              refine ⟨8000196765133356907191841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10666929020177809209589121 8000196765133356907191841)
              ·
                refine ⟨6000147573850017680393881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8000196765133356907191841 6000147573850017680393881)
                ·
                  refine ⟨4500110680387513260295411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000147573850017680393881 4500110680387513260295411)
                  ·
                    refine ⟨6750166020581269890443117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500110680387513260295411 6750166020581269890443117)
                    ·
                      refine ⟨2531312257717976208916169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750166020581269890443117 2531312257717976208916169)
                      ·
                        rfl

theorem cell23_4929713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4929713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929713 prefixEnd_4929713 := by exact prefixLift 4929713
  have htrace : WordTrace (prefixWord ++ tailWord_4929713) baseStart_4929713 baseEnd_4929713 := by
    simpa [prefixWord, tailWord_4929713, baseEnd_4929713] using wordTrace_append hprefix tailTrace_4929713
  have hstable : (prefixWord ++ tailWord_4929713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929713).length < 2 ^ (prefixWord ++ tailWord_4929713).sum := by decide
  have hdescent : baseEnd_4929713 < baseStart_4929713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929715 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_4929715 : Nat := 118140960795 + 4929715 * 2 ^ 59
def prefixEnd_4929715 : Nat := 4983230072969 + 3 ^ 40 * 4929715 * 2
def baseEnd_4929715 : Nat := 2531313284679285201091159

theorem tailTrace_4929715 : CollatzResearch.WordTrace tailWord_4929715 prefixEnd_4929715 2531313284679285201091159 := by
  unfold tailWord_4929715
  simp only [CollatzResearch.WordTrace]
  refine ⟨179801477335491958137774599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119867651556994638758516399 179801477335491958137774599)
  ·
    refine ⟨269702216003237937206661899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179801477335491958137774599 269702216003237937206661899)
    ·
      refine ⟨404553324004856905809992849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269702216003237937206661899 404553324004856905809992849)
      ·
        refine ⟨303414993003642679357494637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404553324004856905809992849 303414993003642679357494637)
        ·
          refine ⟨113780622376366004759060489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303414993003642679357494637 113780622376366004759060489)
          ·
            refine ⟨85335466782274503569295367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113780622376366004759060489 85335466782274503569295367)
            ·
              refine ⟨128003200173411755353943051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85335466782274503569295367 128003200173411755353943051)
              ·
                refine ⟨192004800260117633030914577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128003200173411755353943051 192004800260117633030914577)
                ·
                  refine ⟨144003600195088224773185933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192004800260117633030914577 144003600195088224773185933)
                  ·
                    refine ⟨54001350073158084289944725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144003600195088224773185933 54001350073158084289944725)
                    ·
                      refine ⟨2531313284679285201091159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54001350073158084289944725 2531313284679285201091159)
                      ·
                        rfl

theorem cell23_4929715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_4929715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929715 prefixEnd_4929715 := by exact prefixLift 4929715
  have htrace : WordTrace (prefixWord ++ tailWord_4929715) baseStart_4929715 baseEnd_4929715 := by
    simpa [prefixWord, tailWord_4929715, baseEnd_4929715] using wordTrace_append hprefix tailTrace_4929715
  have hstable : (prefixWord ++ tailWord_4929715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929715).length < 2 ^ (prefixWord ++ tailWord_4929715).sum := by decide
  have hdescent : baseEnd_4929715 < baseStart_4929715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929722 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_4929722 : Nat := 118140960795 + 4929722 * 2 ^ 59
def prefixEnd_4929722 : Nat := 4983230072969 + 3 ^ 40 * 4929722 * 2
def baseEnd_4929722 : Nat := 2531316879043866673703627

theorem tailTrace_4929722 : CollatzResearch.WordTrace tailWord_4929722 prefixEnd_4929722 2531316879043866673703627 := by
  unfold tailWord_4929722
  simp only [CollatzResearch.WordTrace]
  refine ⟨44950433161616649583319855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119867821764311065555519613 44950433161616649583319855)
  ·
    refine ⟨67425649742424974374979783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44950433161616649583319855 67425649742424974374979783)
    ·
      refine ⟨101138474613637461562469675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67425649742424974374979783 101138474613637461562469675)
      ·
        refine ⟨151707711920456192343704513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101138474613637461562469675 151707711920456192343704513)
        ·
          refine ⟨113780783940342144257778385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151707711920456192343704513 113780783940342144257778385)
          ·
            refine ⟨85335587955256608193333789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113780783940342144257778385 85335587955256608193333789)
            ·
              refine ⟨32000845483221228072500171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85335587955256608193333789 32000845483221228072500171)
              ·
                refine ⟨48001268224831842108750257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32000845483221228072500171 48001268224831842108750257)
                ·
                  refine ⟨36000951168623881581562693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48001268224831842108750257 36000951168623881581562693)
                  ·
                    refine ⟨6750178344116977796543005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36000951168623881581562693 6750178344116977796543005)
                    ·
                      refine ⟨2531316879043866673703627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750178344116977796543005 2531316879043866673703627)
                      ·
                        rfl

theorem cell23_4929722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_4929722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929722 prefixEnd_4929722 := by exact prefixLift 4929722
  have htrace : WordTrace (prefixWord ++ tailWord_4929722) baseStart_4929722 baseEnd_4929722 := by
    simpa [prefixWord, tailWord_4929722, baseEnd_4929722] using wordTrace_append hprefix tailTrace_4929722
  have hstable : (prefixWord ++ tailWord_4929722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929722).length < 2 ^ (prefixWord ++ tailWord_4929722).sum := by decide
  have hdescent : baseEnd_4929722 < baseStart_4929722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929730 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4929730 : Nat := 118140960795 + 4929730 * 2 ^ 59
def prefixEnd_4929730 : Nat := 4983230072969 + 3 ^ 40 * 4929730 * 2
def baseEnd_4929730 : Nat := 2531320986889102642403591

theorem tailTrace_4929730 : CollatzResearch.WordTrace tailWord_4929730 prefixEnd_4929730 2531320986889102642403591 := by
  unfold tailWord_4929730
  simp only [CollatzResearch.WordTrace]
  refine ⟨44950506107609403924892661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119868016286958410466380429 44950506107609403924892661)
  ·
    refine ⟨4214109947588381617958687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44950506107609403924892661 4214109947588381617958687)
    ·
      refine ⟨6321164921382572426938031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4214109947588381617958687 6321164921382572426938031)
      ·
        refine ⟨9481747382073858640407047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6321164921382572426938031 9481747382073858640407047)
        ·
          refine ⟨14222621073110787960610571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9481747382073858640407047 14222621073110787960610571)
          ·
            refine ⟨21333931609666181940915857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14222621073110787960610571 21333931609666181940915857)
            ·
              refine ⟨16000448707249636455686893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21333931609666181940915857 16000448707249636455686893)
              ·
                refine ⟨6000168265218613670882585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16000448707249636455686893 6000168265218613670882585)
                ·
                  refine ⟨4500126198913960253161939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000168265218613670882585 4500126198913960253161939)
                  ·
                    refine ⟨6750189298370940379742909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500126198913960253161939 6750189298370940379742909)
                    ·
                      refine ⟨2531320986889102642403591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750189298370940379742909 2531320986889102642403591)
                      ·
                        rfl

theorem cell23_4929730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4929730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929730 prefixEnd_4929730 := by exact prefixLift 4929730
  have htrace : WordTrace (prefixWord ++ tailWord_4929730) baseStart_4929730 baseEnd_4929730 := by
    simpa [prefixWord, tailWord_4929730, baseEnd_4929730] using wordTrace_append hprefix tailTrace_4929730
  have hstable : (prefixWord ++ tailWord_4929730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929730).length < 2 ^ (prefixWord ++ tailWord_4929730).sum := by decide
  have hdescent : baseEnd_4929730 < baseStart_4929730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929742 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_4929742 : Nat := 118140960795 + 4929742 * 2 ^ 59
def prefixEnd_4929742 : Nat := 4983230072969 + 3 ^ 40 * 4929742 * 2
def baseEnd_4929742 : Nat := 281258572072995177272615

theorem tailTrace_4929742 : CollatzResearch.WordTrace tailWord_4929742 prefixEnd_4929742 281258572072995177272615 := by
  unfold tailWord_4929742
  simp only [CollatzResearch.WordTrace]
  refine ⟨22475307763299267718625935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119868308070929427832671653 22475307763299267718625935)
  ·
    refine ⟨33712961644948901577938903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22475307763299267718625935 33712961644948901577938903)
    ·
      refine ⟨50569442467423352366908355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33712961644948901577938903 50569442467423352366908355)
      ·
        refine ⟨75854163701135028550362533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50569442467423352366908355 75854163701135028550362533)
        ·
          refine ⟨14222655693962817853192975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75854163701135028550362533 14222655693962817853192975)
          ·
            refine ⟨21333983540944226779789463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14222655693962817853192975 21333983540944226779789463)
            ·
              refine ⟨32000975311416340169684195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21333983540944226779789463 32000975311416340169684195)
              ·
                refine ⟨48001462967124510254526293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32000975311416340169684195 48001462967124510254526293)
                ·
                  refine ⟨281258572072995177272615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48001462967124510254526293 281258572072995177272615)
                  ·
                    rfl

theorem cell23_4929742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_4929742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929742 prefixEnd_4929742 := by exact prefixLift 4929742
  have htrace : WordTrace (prefixWord ++ tailWord_4929742) baseStart_4929742 baseEnd_4929742 := by
    simpa [prefixWord, tailWord_4929742, baseEnd_4929742] using wordTrace_append hprefix tailTrace_4929742
  have hstable : (prefixWord ++ tailWord_4929742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929742).length < 2 ^ (prefixWord ++ tailWord_4929742).sum := by decide
  have hdescent : baseEnd_4929742 < baseStart_4929742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929772 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_4929772 : Nat := 118140960795 + 4929772 * 2 ^ 59
def prefixEnd_4929772 : Nat := 4983230072969 + 3 ^ 40 * 4929772 * 2
def baseEnd_4929772 : Nat := 843780851025530492692799

theorem tailTrace_4929772 : CollatzResearch.WordTrace tailWord_4929772 prefixEnd_4929772 843780851025530492692799 := by
  unfold tailWord_4929772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89901778148142728436299785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119869037530856971248399713 89901778148142728436299785)
  ·
    refine ⟨67426333611107046327224839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89901778148142728436299785 67426333611107046327224839)
    ·
      refine ⟨101139500416660569490837259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67426333611107046327224839 101139500416660569490837259)
      ·
        refine ⟨151709250624990854236255889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101139500416660569490837259 151709250624990854236255889)
        ·
          refine ⟨113781937968743140677191917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151709250624990854236255889 113781937968743140677191917)
          ·
            refine ⟨42668226738278677753946969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113781937968743140677191917 42668226738278677753946969)
            ·
              refine ⟨32001170053709008315460227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42668226738278677753946969 32001170053709008315460227)
              ·
                refine ⟨48001755080563512473190341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32001170053709008315460227 48001755080563512473190341)
                ·
                  refine ⟨9000329077605658588723189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48001755080563512473190341 9000329077605658588723189)
                  ·
                    refine ⟨843780851025530492692799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9000329077605658588723189 843780851025530492692799)
                    ·
                      rfl

theorem cell23_4929772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_4929772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929772 prefixEnd_4929772 := by exact prefixLift 4929772
  have htrace : WordTrace (prefixWord ++ tailWord_4929772) baseStart_4929772 baseEnd_4929772 := by
    simpa [prefixWord, tailWord_4929772, baseEnd_4929772] using wordTrace_append hprefix tailTrace_4929772
  have hstable : (prefixWord ++ tailWord_4929772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929772).length < 2 ^ (prefixWord ++ tailWord_4929772).sum := by decide
  have hdescent : baseEnd_4929772 < baseStart_4929772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929792 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_4929792 : Nat := 118140960795 + 4929792 * 2 ^ 59
def prefixEnd_4929792 : Nat := 4983230072969 + 3 ^ 40 * 4929792 * 2
def baseEnd_4929792 : Nat := 2531352822689681399828305

theorem tailTrace_4929792 : CollatzResearch.WordTrace tailWord_4929792 prefixEnd_4929792 2531352822689681399828305 := by
  unfold tailWord_4929792
  simp only [CollatzResearch.WordTrace]
  refine ⟨89902142878106500144163815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119869523837475333525551753 89902142878106500144163815)
  ·
    refine ⟨134853214317159750216245723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89902142878106500144163815 134853214317159750216245723)
    ·
      refine ⟨202279821475739625324368585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134853214317159750216245723 202279821475739625324368585)
      ·
        refine ⟨151709866106804718993276439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202279821475739625324368585 151709866106804718993276439)
        ·
          refine ⟨227564799160207078489914659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151709866106804718993276439 227564799160207078489914659)
          ·
            refine ⟨341347198740310617734871989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227564799160207078489914659 341347198740310617734871989)
            ·
              refine ⟨32001299881904120412644249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 341347198740310617734871989 32001299881904120412644249)
              ·
                refine ⟨24000974911428090309483187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32001299881904120412644249 24000974911428090309483187)
                ·
                  refine ⟨36001462367142135464224781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24000974911428090309483187 36001462367142135464224781)
                  ·
                    refine ⟨13500548387678300799084293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36001462367142135464224781 13500548387678300799084293)
                    ·
                      refine ⟨2531352822689681399828305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13500548387678300799084293 2531352822689681399828305)
                      ·
                        rfl

theorem cell23_4929792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_4929792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929792 prefixEnd_4929792 := by exact prefixLift 4929792
  have htrace : WordTrace (prefixWord ++ tailWord_4929792) baseStart_4929792 baseEnd_4929792 := by
    simpa [prefixWord, tailWord_4929792, baseEnd_4929792] using wordTrace_append hprefix tailTrace_4929792
  have hstable : (prefixWord ++ tailWord_4929792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929792).length < 2 ^ (prefixWord ++ tailWord_4929792).sum := by decide
  have hdescent : baseEnd_4929792 < baseStart_4929792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929826 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4929826 : Nat := 118140960795 + 4929826 * 2 ^ 59
def prefixEnd_4929826 : Nat := 4983230072969 + 3 ^ 40 * 4929826 * 2
def baseEnd_4929826 : Nat := 2531370281031934266803149

theorem tailTrace_4929826 : CollatzResearch.WordTrace tailWord_4929826 prefixEnd_4929826 2531370281031934266803149 := by
  unfold tailWord_4929826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44951381459522456023766333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119870350558726549396710221 44951381459522456023766333)
  ·
    refine ⟨16856768047320921008912375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44951381459522456023766333 16856768047320921008912375)
    ·
      refine ⟨25285152070981381513368563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16856768047320921008912375 25285152070981381513368563)
      ·
        refine ⟨37927728106472072270052845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25285152070981381513368563 37927728106472072270052845)
        ·
          refine ⟨14222898039927027101269817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37927728106472072270052845 14222898039927027101269817)
          ·
            refine ⟨10667173529945270325952363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14222898039927027101269817 10667173529945270325952363)
            ·
              refine ⟨16000760294917905488928545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10667173529945270325952363 16000760294917905488928545)
              ·
                refine ⟨12000570221188429116696409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16000760294917905488928545 12000570221188429116696409)
                ·
                  refine ⟨9000427665891321837522307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12000570221188429116696409 9000427665891321837522307)
                  ·
                    refine ⟨13500641498836982756283461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9000427665891321837522307 13500641498836982756283461)
                    ·
                      refine ⟨2531370281031934266803149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13500641498836982756283461 2531370281031934266803149)
                      ·
                        rfl

theorem cell23_4929826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4929826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929826 prefixEnd_4929826 := by exact prefixLift 4929826
  have htrace : WordTrace (prefixWord ++ tailWord_4929826) baseStart_4929826 baseEnd_4929826 := by
    simpa [prefixWord, tailWord_4929826, baseEnd_4929826] using wordTrace_append hprefix tailTrace_4929826
  have hstable : (prefixWord ++ tailWord_4929826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929826).length < 2 ^ (prefixWord ++ tailWord_4929826).sum := by decide
  have hdescent : baseEnd_4929826 < baseStart_4929826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929836 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_4929836 : Nat := 118140960795 + 4929836 * 2 ^ 59
def prefixEnd_4929836 : Nat := 4983230072969 + 3 ^ 40 * 4929836 * 2
def baseEnd_4929836 : Nat := 843791805279493075892701

theorem tailTrace_4929836 : CollatzResearch.WordTrace tailWord_4929836 prefixEnd_4929836 843791805279493075892701 := by
  unfold tailWord_4929836
  simp only [CollatzResearch.WordTrace]
  refine ⟨89902945284026797901464681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119870593712035730535286241 89902945284026797901464681)
  ·
    refine ⟨67427208963020098426098511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89902945284026797901464681 67427208963020098426098511)
    ·
      refine ⟨101140813444530147639147767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67427208963020098426098511 101140813444530147639147767)
      ·
        refine ⟨151711220166795221458721651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101140813444530147639147767 151711220166795221458721651)
        ·
          refine ⟨227566830250192832188082477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151711220166795221458721651 227566830250192832188082477)
          ·
            refine ⟨85337561343822312070530929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227566830250192832188082477 85337561343822312070530929)
            ·
              refine ⟨64003171007866734052898197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85337561343822312070530929 64003171007866734052898197)
              ·
                refine ⟨3000148640993753158729603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64003171007866734052898197 3000148640993753158729603)
                ·
                  refine ⟨4500222961490629738094405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000148640993753158729603 4500222961490629738094405)
                  ·
                    refine ⟨843791805279493075892701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4500222961490629738094405 843791805279493075892701)
                    ·
                      rfl

theorem cell23_4929836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_4929836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929836 prefixEnd_4929836 := by exact prefixLift 4929836
  have htrace : WordTrace (prefixWord ++ tailWord_4929836) baseStart_4929836 baseEnd_4929836 := by
    simpa [prefixWord, tailWord_4929836, baseEnd_4929836] using wordTrace_append hprefix tailTrace_4929836
  have hstable : (prefixWord ++ tailWord_4929836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929836).length < 2 ^ (prefixWord ++ tailWord_4929836).sum := by decide
  have hdescent : baseEnd_4929836 < baseStart_4929836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929953 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4929953 : Nat := 118140960795 + 4929953 * 2 ^ 59
def prefixEnd_4929953 : Nat := 4983230072969 + 3 ^ 40 * 4929953 * 2
def baseEnd_4929953 : Nat := 2531435493075055269915065

theorem tailTrace_4929953 : CollatzResearch.WordTrace tailWord_4929953 prefixEnd_4929953 2531435493075055269915065 := by
  unfold tailWord_4929953
  simp only [CollatzResearch.WordTrace]
  refine ⟨179810157908629724784938513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119873438605753149856625675 179810157908629724784938513)
  ·
    refine ⟨134857618431472293588703885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179810157908629724784938513 134857618431472293588703885)
    ·
      refine ⟨50571606911802110095763957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134857618431472293588703885 50571606911802110095763957)
      ·
        refine ⟨4741088147981447821477871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50571606911802110095763957 4741088147981447821477871)
        ·
          refine ⟨7111632221972171732216807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741088147981447821477871 7111632221972171732216807)
          ·
            refine ⟨10667448332958257598325211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111632221972171732216807 10667448332958257598325211)
            ·
              refine ⟨16001172499437386397487817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10667448332958257598325211 16001172499437386397487817)
              ·
                refine ⟨12000879374578039798115863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16001172499437386397487817 12000879374578039798115863)
                ·
                  refine ⟨18001319061867059697173795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12000879374578039798115863 18001319061867059697173795)
                  ·
                    refine ⟨27001978592800589545760693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18001319061867059697173795 27001978592800589545760693)
                    ·
                      refine ⟨2531435493075055269915065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27001978592800589545760693 2531435493075055269915065)
                      ·
                        rfl

theorem cell23_4929953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4929953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929953 prefixEnd_4929953 := by exact prefixLift 4929953
  have htrace : WordTrace (prefixWord ++ tailWord_4929953) baseStart_4929953 baseEnd_4929953 := by
    simpa [prefixWord, tailWord_4929953, baseEnd_4929953] using wordTrace_append hprefix tailTrace_4929953
  have hstable : (prefixWord ++ tailWord_4929953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929953).length < 2 ^ (prefixWord ++ tailWord_4929953).sum := by decide
  have hdescent : baseEnd_4929953 < baseStart_4929953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929973 : List Nat := [1, 3, 3, 2, 3, 2, 2, 7]
def baseStart_4929973 : Nat := 118140960795 + 4929973 * 2 ^ 59
def prefixEnd_4929973 : Nat := 4983230072969 + 3 ^ 40 * 4929973 * 2
def baseEnd_4929973 : Nat := 93757250469931303394999

theorem tailTrace_4929973 : CollatzResearch.WordTrace tailWord_4929973 prefixEnd_4929973 93757250469931303394999 := by
  unfold tailWord_4929973
  simp only [CollatzResearch.WordTrace]
  refine ⟨179810887368557268200666573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119873924912371512133777715 179810887368557268200666573)
  ·
    refine ⟨67429082763208975575249965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179810887368557268200666573 67429082763208975575249965)
    ·
      refine ⟨25285906036203365840718737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67429082763208975575249965 25285906036203365840718737)
      ·
        refine ⟨18964429527152524380539053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25285906036203365840718737 18964429527152524380539053)
        ·
          refine ⟨7111661072682196642702145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18964429527152524380539053 7111661072682196642702145)
          ·
            refine ⟨5333745804511647482026609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7111661072682196642702145 5333745804511647482026609)
            ·
              refine ⟨4000309353383735611519957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5333745804511647482026609 4000309353383735611519957)
              ·
                refine ⟨93757250469931303394999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4000309353383735611519957 93757250469931303394999)
                ·
                  rfl

theorem cell23_4929973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 7].length) (baseStart_4929973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929973 prefixEnd_4929973 := by exact prefixLift 4929973
  have htrace : WordTrace (prefixWord ++ tailWord_4929973) baseStart_4929973 baseEnd_4929973 := by
    simpa [prefixWord, tailWord_4929973, baseEnd_4929973] using wordTrace_append hprefix tailTrace_4929973
  have hstable : (prefixWord ++ tailWord_4929973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929973).length < 2 ^ (prefixWord ++ tailWord_4929973).sum := by decide
  have hdescent : baseEnd_4929973 < baseStart_4929973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4929993 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 1, 3, 2]
def baseStart_4929993 : Nat := 118140960795 + 4929993 * 2 ^ 59
def prefixEnd_4929993 : Nat := 4983230072969 + 3 ^ 40 * 4929993 * 2
def baseEnd_4929993 : Nat := 2531456032301235113414881

theorem tailTrace_4929993 : CollatzResearch.WordTrace tailWord_4929993 prefixEnd_4929993 2531456032301235113414881 := by
  unfold tailWord_4929993
  simp only [CollatzResearch.WordTrace]
  refine ⟨179811616828484811616394633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119874411218989874410929755 179811616828484811616394633)
  ·
    refine ⟨134858712621363608712295975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179811616828484811616394633 134858712621363608712295975)
    ·
      refine ⟨202288068932045413068443963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134858712621363608712295975 202288068932045413068443963)
      ·
        refine ⟨303432103398068119602665945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202288068932045413068443963 303432103398068119602665945)
        ·
          refine ⟨227574077548551089701999459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303432103398068119602665945 227574077548551089701999459)
          ·
            refine ⟨341361116322826634552999189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227574077548551089701999459 341361116322826634552999189)
            ·
              refine ⟨16001302327632498494671837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 341361116322826634552999189 16001302327632498494671837)
              ·
                refine ⟨6000488372862186935501939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16001302327632498494671837 6000488372862186935501939)
                ·
                  refine ⟨9000732559293280403252909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6000488372862186935501939 9000732559293280403252909)
                  ·
                    refine ⟨3375274709734980151219841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9000732559293280403252909 3375274709734980151219841)
                    ·
                      refine ⟨2531456032301235113414881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375274709734980151219841 2531456032301235113414881)
                      ·
                        rfl

theorem cell23_4929993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 3, 2].length) (baseStart_4929993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4929993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4929993 prefixEnd_4929993 := by exact prefixLift 4929993
  have htrace : WordTrace (prefixWord ++ tailWord_4929993) baseStart_4929993 baseEnd_4929993 := by
    simpa [prefixWord, tailWord_4929993, baseEnd_4929993] using wordTrace_append hprefix tailTrace_4929993
  have hstable : (prefixWord ++ tailWord_4929993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4929993).length < 2 ^ (prefixWord ++ tailWord_4929993).sum := by decide
  have hdescent : baseEnd_4929993 < baseStart_4929993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4929993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930009 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_4930009 : Nat := 118140960795 + 4930009 * 2 ^ 59
def prefixEnd_4930009 : Nat := 4983230072969 + 3 ^ 40 * 4930009 * 2
def baseEnd_4930009 : Nat := 2531464247991707050814807

theorem tailTrace_4930009 : CollatzResearch.WordTrace tailWord_4930009 prefixEnd_4930009 2531464247991707050814807 := by
  unfold tailWord_4930009
  simp only [CollatzResearch.WordTrace]
  refine ⟨179812200396426846348977081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119874800264284564232651387 179812200396426846348977081)
  ·
    refine ⟨134859150297320134761732811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179812200396426846348977081 134859150297320134761732811)
    ·
      refine ⟨202288725445980202142599217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134859150297320134761732811 202288725445980202142599217)
      ·
        refine ⟨151716544084485151606949413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202288725445980202142599217 151716544084485151606949413)
        ·
          refine ⟨28446852015840965926303015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151716544084485151606949413 28446852015840965926303015)
          ·
            refine ⟨42670278023761448889454523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28446852015840965926303015 42670278023761448889454523)
            ·
              refine ⟨64005417035642173334181785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42670278023761448889454523 64005417035642173334181785)
              ·
                refine ⟨48004062776731630000636339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64005417035642173334181785 48004062776731630000636339)
                ·
                  refine ⟨72006094165097445000954509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48004062776731630000636339 72006094165097445000954509)
                  ·
                    refine ⟨27002285311911541875357941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72006094165097445000954509 27002285311911541875357941)
                    ·
                      refine ⟨2531464247991707050814807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27002285311911541875357941 2531464247991707050814807)
                      ·
                        rfl

theorem cell23_4930009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_4930009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930009 prefixEnd_4930009 := by exact prefixLift 4930009
  have htrace : WordTrace (prefixWord ++ tailWord_4930009) baseStart_4930009 baseEnd_4930009 := by
    simpa [prefixWord, tailWord_4930009, baseEnd_4930009] using wordTrace_append hprefix tailTrace_4930009
  have hstable : (prefixWord ++ tailWord_4930009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930009).length < 2 ^ (prefixWord ++ tailWord_4930009).sum := by decide
  have hdescent : baseEnd_4930009 < baseStart_4930009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930023 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4930023 : Nat := 118140960795 + 4930023 * 2 ^ 59
def prefixEnd_4930023 : Nat := 4983230072969 + 3 ^ 40 * 4930023 * 2
def baseEnd_4930023 : Nat := 2531471436720869996039743

theorem tailTrace_4930023 : CollatzResearch.WordTrace tailWord_4930023 prefixEnd_4930023 2531471436720869996039743 := by
  unfold tailWord_4930023
  simp only [CollatzResearch.WordTrace]
  refine ⟨179812711018376126739986723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119875140678917417826657815 179812711018376126739986723)
  ·
    refine ⟨269719066527564190109980085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179812711018376126739986723 269719066527564190109980085)
    ·
      refine ⟨25286162486959142822810633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269719066527564190109980085 25286162486959142822810633)
      ·
        refine ⟨18964621865219357117107975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25286162486959142822810633 18964621865219357117107975)
        ·
          refine ⟨28446932797829035675661963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18964621865219357117107975 28446932797829035675661963)
          ·
            refine ⟨42670399196743553513492945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28446932797829035675661963 42670399196743553513492945)
            ·
              refine ⟨32002799397557665135119709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42670399196743553513492945 32002799397557665135119709)
              ·
                refine ⟨12001049774084124425669891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32002799397557665135119709 12001049774084124425669891)
                ·
                  refine ⟨18001574661126186638504837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12001049774084124425669891 18001574661126186638504837)
                  ·
                    refine ⟨3375295248961159994719657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18001574661126186638504837 3375295248961159994719657)
                    ·
                      refine ⟨2531471436720869996039743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375295248961159994719657 2531471436720869996039743)
                      ·
                        rfl

theorem cell23_4930023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4930023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930023 prefixEnd_4930023 := by exact prefixLift 4930023
  have htrace : WordTrace (prefixWord ++ tailWord_4930023) baseStart_4930023 baseEnd_4930023 := by
    simpa [prefixWord, tailWord_4930023, baseEnd_4930023] using wordTrace_append hprefix tailTrace_4930023
  have hstable : (prefixWord ++ tailWord_4930023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930023).length < 2 ^ (prefixWord ++ tailWord_4930023).sum := by decide
  have hdescent : baseEnd_4930023 < baseStart_4930023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930026 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_4930026 : Nat := 118140960795 + 4930026 * 2 ^ 59
def prefixEnd_4930026 : Nat := 4983230072969 + 3 ^ 40 * 4930026 * 2
def baseEnd_4930026 : Nat := 2531472977162833484302229

theorem tailTrace_4930026 : CollatzResearch.WordTrace tailWord_4930026 prefixEnd_4930026 2531472977162833484302229 := by
  unfold tailWord_4930026
  simp only [CollatzResearch.WordTrace]
  refine ⟨44953205109341314563086483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119875213624910172168230621 44953205109341314563086483)
  ·
    refine ⟨67429807664011971844629725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44953205109341314563086483 67429807664011971844629725)
    ·
      refine ⟨25286177874004489441736147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67429807664011971844629725 25286177874004489441736147)
      ·
        refine ⟨37929266811006734162604221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25286177874004489441736147 37929266811006734162604221)
        ·
          refine ⟨14223475054127525310976583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37929266811006734162604221 14223475054127525310976583)
          ·
            refine ⟨21335212581191287966464875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14223475054127525310976583 21335212581191287966464875)
            ·
              refine ⟨32002818871786931949697313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21335212581191287966464875 32002818871786931949697313)
              ·
                refine ⟨24002114153840198962272985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32002818871786931949697313 24002114153840198962272985)
                ·
                  refine ⟨18001585615380149221704739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24002114153840198962272985 18001585615380149221704739)
                  ·
                    refine ⟨27002378423070223832557109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18001585615380149221704739 27002378423070223832557109)
                    ·
                      refine ⟨2531472977162833484302229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27002378423070223832557109 2531472977162833484302229)
                      ·
                        rfl

theorem cell23_4930026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_4930026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930026 prefixEnd_4930026 := by exact prefixLift 4930026
  have htrace : WordTrace (prefixWord ++ tailWord_4930026) baseStart_4930026 baseEnd_4930026 := by
    simpa [prefixWord, tailWord_4930026, baseEnd_4930026] using wordTrace_append hprefix tailTrace_4930026
  have hstable : (prefixWord ++ tailWord_4930026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930026).length < 2 ^ (prefixWord ++ tailWord_4930026).sum := by decide
  have hdescent : baseEnd_4930026 < baseStart_4930026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930056 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_4930056 : Nat := 118140960795 + 4930056 * 2 ^ 59
def prefixEnd_4930056 : Nat := 4983230072969 + 3 ^ 40 * 4930056 * 2
def baseEnd_4930056 : Nat := 2531488381582468366927091

theorem tailTrace_4930056 : CollatzResearch.WordTrace tailWord_4930056 prefixEnd_4930056 2531488381582468366927091 := by
  unfold tailWord_4930056
  simp only [CollatzResearch.WordTrace]
  refine ⟨89906957313628286687969011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119875943084837715583958681 89906957313628286687969011)
  ·
    refine ⟨134860435970442430031953517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89906957313628286687969011 134860435970442430031953517)
    ·
      refine ⟨50572663488915911261982569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134860435970442430031953517 50572663488915911261982569)
      ·
        refine ⟨37929497616686933446486927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50572663488915911261982569 37929497616686933446486927)
        ·
          refine ⟨56894246425030400169730391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37929497616686933446486927 56894246425030400169730391)
          ·
            refine ⟨85341369637545600254595587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56894246425030400169730391 85341369637545600254595587)
            ·
              refine ⟨128012054456318400381893381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85341369637545600254595587 128012054456318400381893381)
              ·
                refine ⟨24002260210559700071605009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128012054456318400381893381 24002260210559700071605009)
                ·
                  refine ⟨18001695157919775053703757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24002260210559700071605009 18001695157919775053703757)
                  ·
                    refine ⟨6750635684219915645138909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18001695157919775053703757 6750635684219915645138909)
                    ·
                      refine ⟨2531488381582468366927091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750635684219915645138909 2531488381582468366927091)
                      ·
                        rfl

theorem cell23_4930056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_4930056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930056 prefixEnd_4930056 := by exact prefixLift 4930056
  have htrace : WordTrace (prefixWord ++ tailWord_4930056) baseStart_4930056 baseEnd_4930056 := by
    simpa [prefixWord, tailWord_4930056, baseEnd_4930056] using wordTrace_append hprefix tailTrace_4930056
  have hstable : (prefixWord ++ tailWord_4930056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930056).length < 2 ^ (prefixWord ++ tailWord_4930056).sum := by decide
  have hdescent : baseEnd_4930056 < baseStart_4930056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930136 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 6]
def baseStart_4930136 : Nat := 118140960795 + 4930136 * 2 ^ 59
def prefixEnd_4930136 : Nat := 4983230072969 + 3 ^ 40 * 4930136 * 2
def baseEnd_4930136 : Nat := 281281051114980894880747

theorem tailTrace_4930136 : CollatzResearch.WordTrace tailWord_4930136 prefixEnd_4930136 281281051114980894880747 := by
  unfold tailWord_4930136
  simp only [CollatzResearch.WordTrace]
  refine ⟨89908416233483373519425131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119877888311311164692566841 89908416233483373519425131)
  ·
    refine ⟨134862624350225060279137697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89908416233483373519425131 134862624350225060279137697)
    ·
      refine ⟨101146968262668795209353273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134862624350225060279137697 101146968262668795209353273)
      ·
        refine ⟨75860226197001596407014955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101146968262668795209353273 75860226197001596407014955)
        ·
          refine ⟨113790339295502394610522433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75860226197001596407014955 113790339295502394610522433)
          ·
            refine ⟨85342754471626795957891825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113790339295502394610522433 85342754471626795957891825)
            ·
              refine ⟨64007065853720096968418869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85342754471626795957891825 64007065853720096968418869)
              ·
                refine ⟨6000662423786259090789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64007065853720096968418869 6000662423786259090789269)
                ·
                  refine ⟨281281051114980894880747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6000662423786259090789269 281281051114980894880747)
                  ·
                    rfl

theorem cell23_4930136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_4930136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930136 prefixEnd_4930136 := by exact prefixLift 4930136
  have htrace : WordTrace (prefixWord ++ tailWord_4930136) baseStart_4930136 baseEnd_4930136 := by
    simpa [prefixWord, tailWord_4930136, baseEnd_4930136] using wordTrace_append hprefix tailTrace_4930136
  have hstable : (prefixWord ++ tailWord_4930136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930136).length < 2 ^ (prefixWord ++ tailWord_4930136).sum := by decide
  have hdescent : baseEnd_4930136 < baseStart_4930136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930157 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_4930157 : Nat := 118140960795 + 4930157 * 2 ^ 59
def prefixEnd_4930157 : Nat := 4983230072969 + 3 ^ 40 * 4930157 * 2
def baseEnd_4930157 : Nat := 843846747709524157254709

theorem tailTrace_4930157 : CollatzResearch.WordTrace tailWord_4930157 prefixEnd_4930157 843846747709524157254709 := by
  unfold tailWord_4930157
  simp only [CollatzResearch.WordTrace]
  refine ⟨179817598399890667625364725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119878398933260445083576483 179817598399890667625364725)
  ·
    refine ⟨16857899849989750089877943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179817598399890667625364725 16857899849989750089877943)
    ·
      refine ⟨25286849774984625134816915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16857899849989750089877943 25286849774984625134816915)
      ·
        refine ⟨37930274662476937702225373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25286849774984625134816915 37930274662476937702225373)
        ·
          refine ⟨14223852998428851638334515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37930274662476937702225373 14223852998428851638334515)
          ·
            refine ⟨21335779497643277457501773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14223852998428851638334515 21335779497643277457501773)
            ·
              refine ⟨8000917311616229046563165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21335779497643277457501773 8000917311616229046563165)
              ·
                refine ⟨3000343991856085892461187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8000917311616229046563165 3000343991856085892461187)
                ·
                  refine ⟨4500515987784128838691781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000343991856085892461187 4500515987784128838691781)
                  ·
                    refine ⟨843846747709524157254709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4500515987784128838691781 843846747709524157254709)
                    ·
                      rfl

theorem cell23_4930157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_4930157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930157 prefixEnd_4930157 := by exact prefixLift 4930157
  have htrace : WordTrace (prefixWord ++ tailWord_4930157) baseStart_4930157 baseEnd_4930157 := by
    simpa [prefixWord, tailWord_4930157, baseEnd_4930157] using wordTrace_append hprefix tailTrace_4930157
  have hstable : (prefixWord ++ tailWord_4930157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930157).length < 2 ^ (prefixWord ++ tailWord_4930157).sum := by decide
  have hdescent : baseEnd_4930157 < baseStart_4930157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930190 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4930190 : Nat := 118140960795 + 4930190 * 2 ^ 59
def prefixEnd_4930190 : Nat := 4983230072969 + 3 ^ 40 * 4930190 * 2
def baseEnd_4930190 : Nat := 2531557187990170842651475

theorem tailTrace_4930190 : CollatzResearch.WordTrace tailWord_4930190 prefixEnd_4930190 2531557187990170842651475 := by
  unfold tailWord_4930190
  simp only [CollatzResearch.WordTrace]
  refine ⟨22477350251096389282664503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119879201339180742840877349 22477350251096389282664503)
  ·
    refine ⟨33716025376644583923996755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22477350251096389282664503 33716025376644583923996755)
    ·
      refine ⟨50574038064966875885995133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33716025376644583923996755 50574038064966875885995133)
      ·
        refine ⟨18965264274362578457248175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50574038064966875885995133 18965264274362578457248175)
        ·
          refine ⟨28447896411543867685872263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18965264274362578457248175 28447896411543867685872263)
          ·
            refine ⟨42671844617315801528808395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28447896411543867685872263 42671844617315801528808395)
            ·
              refine ⟨64007766925973702293212593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42671844617315801528808395 64007766925973702293212593)
              ·
                refine ⟨48005825194480276719909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64007766925973702293212593 48005825194480276719909445)
                ·
                  refine ⟨9001092223965051884983021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48005825194480276719909445 9001092223965051884983021)
                  ·
                    refine ⟨3375409583986894456868633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9001092223965051884983021 3375409583986894456868633)
                    ·
                      refine ⟨2531557187990170842651475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375409583986894456868633 2531557187990170842651475)
                      ·
                        rfl

theorem cell23_4930190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4930190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930190 prefixEnd_4930190 := by exact prefixLift 4930190
  have htrace : WordTrace (prefixWord ++ tailWord_4930190) baseStart_4930190 baseEnd_4930190 := by
    simpa [prefixWord, tailWord_4930190, baseEnd_4930190] using wordTrace_append hprefix tailTrace_4930190
  have hstable : (prefixWord ++ tailWord_4930190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930190).length < 2 ^ (prefixWord ++ tailWord_4930190).sum := by decide
  have hdescent : baseEnd_4930190 < baseStart_4930190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930223 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_4930223 : Nat := 118140960795 + 4930223 * 2 ^ 59
def prefixEnd_4930223 : Nat := 4983230072969 + 3 ^ 40 * 4930223 * 2
def baseEnd_4930223 : Nat := 2531574132851769213538823

theorem tailTrace_4930223 : CollatzResearch.WordTrace tailWord_4930223 prefixEnd_4930223 2531574132851769213538823 := by
  unfold tailWord_4930223
  simp only [CollatzResearch.WordTrace]
  refine ⟨179820005617651560897267323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119880003745101040598178215 179820005617651560897267323)
  ·
    refine ⟨269730008426477341345900985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179820005617651560897267323 269730008426477341345900985)
    ·
      refine ⟨202297506319858006009425739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269730008426477341345900985 202297506319858006009425739)
      ·
        refine ⟨303446259479787009014138609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202297506319858006009425739 303446259479787009014138609)
        ·
          refine ⟨227584694609840256760603957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303446259479787009014138609 227584694609840256760603957)
          ·
            refine ⟨21336065119672524071306621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227584694609840256760603957 21336065119672524071306621)
            ·
              refine ⟨8001024419877196526739983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21336065119672524071306621 8001024419877196526739983)
              ·
                refine ⟨12001536629815794790109975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8001024419877196526739983 12001536629815794790109975)
                ·
                  refine ⟨18002304944723692185164963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12001536629815794790109975 18002304944723692185164963)
                  ·
                    refine ⟨27003457417085538277747445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18002304944723692185164963 27003457417085538277747445)
                    ·
                      refine ⟨2531574132851769213538823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27003457417085538277747445 2531574132851769213538823)
                      ·
                        rfl

theorem cell23_4930223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_4930223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930223 prefixEnd_4930223 := by exact prefixLift 4930223
  have htrace : WordTrace (prefixWord ++ tailWord_4930223) baseStart_4930223 baseEnd_4930223 := by
    simpa [prefixWord, tailWord_4930223, baseEnd_4930223] using wordTrace_append hprefix tailTrace_4930223
  have hstable : (prefixWord ++ tailWord_4930223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930223).length < 2 ^ (prefixWord ++ tailWord_4930223).sum := by decide
  have hdescent : baseEnd_4930223 < baseStart_4930223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930231 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 1, 1, 3]
def baseStart_4930231 : Nat := 118140960795 + 4930231 * 2 ^ 59
def prefixEnd_4930231 : Nat := 4983230072969 + 3 ^ 40 * 4930231 * 2
def baseEnd_4930231 : Nat := 2531578240697005182238787

theorem tailTrace_4930231 : CollatzResearch.WordTrace tailWord_4930231 prefixEnd_4930231 2531578240697005182238787 := by
  unfold tailWord_4930231
  simp only [CollatzResearch.WordTrace]
  refine ⟨179820297401622578263558547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119880198267748385509039031 179820297401622578263558547)
  ·
    refine ⟨269730446102433867395337821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179820297401622578263558547 269730446102433867395337821)
    ·
      refine ⟨101148917288412700273251683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269730446102433867395337821 101148917288412700273251683)
      ·
        refine ⟨151723375932619050409877525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101148917288412700273251683 151723375932619050409877525)
        ·
          refine ⟨7112033246841517987963009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151723375932619050409877525 7112033246841517987963009)
          ·
            refine ⟨5334024935131138490972257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7112033246841517987963009 5334024935131138490972257)
            ·
              refine ⟨4000518701348353868229193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5334024935131138490972257 4000518701348353868229193)
              ·
                refine ⟨3000389026011265401171895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000518701348353868229193 3000389026011265401171895)
                ·
                  refine ⟨4500583539016898101757843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000389026011265401171895 4500583539016898101757843)
                  ·
                    refine ⟨6750875308525347152636765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500583539016898101757843 6750875308525347152636765)
                    ·
                      refine ⟨2531578240697005182238787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750875308525347152636765 2531578240697005182238787)
                      ·
                        rfl

theorem cell23_4930231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_4930231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930231 prefixEnd_4930231 := by exact prefixLift 4930231
  have htrace : WordTrace (prefixWord ++ tailWord_4930231) baseStart_4930231 baseEnd_4930231 := by
    simpa [prefixWord, tailWord_4930231, baseEnd_4930231] using wordTrace_append hprefix tailTrace_4930231
  have hstable : (prefixWord ++ tailWord_4930231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930231).length < 2 ^ (prefixWord ++ tailWord_4930231).sum := by decide
  have hdescent : baseEnd_4930231 < baseStart_4930231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930250 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_4930250 : Nat := 118140960795 + 4930250 * 2 ^ 59
def prefixEnd_4930250 : Nat := 4983230072969 + 3 ^ 40 * 4930250 * 2
def baseEnd_4930250 : Nat := 2531587996829440607901199

theorem tailTrace_4930250 : CollatzResearch.WordTrace tailWord_4930250 prefixEnd_4930250 2531587996829440607901199 := by
  unfold tailWord_4930250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44955247597138436127125051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119880660259035829672333469 44955247597138436127125051)
  ·
    refine ⟨67432871395707654190687577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44955247597138436127125051 67432871395707654190687577)
    ·
      refine ⟨50574653546780740643015683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67432871395707654190687577 50574653546780740643015683)
      ·
        refine ⟨75861980320171110964523525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50574653546780740643015683 75861980320171110964523525)
        ·
          refine ⟨14224121310032083305848161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75861980320171110964523525 14224121310032083305848161)
          ·
            refine ⟨10668090982524062479386121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14224121310032083305848161 10668090982524062479386121)
            ·
              refine ⟨8001068236893046859539591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10668090982524062479386121 8001068236893046859539591)
              ·
                refine ⟨12001602355339570289309387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8001068236893046859539591 12001602355339570289309387)
                ·
                  refine ⟨18002403533009355433964081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12001602355339570289309387 18002403533009355433964081)
                  ·
                    refine ⟨13501802649757016575473061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18002403533009355433964081 13501802649757016575473061)
                    ·
                      refine ⟨2531587996829440607901199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13501802649757016575473061 2531587996829440607901199)
                      ·
                        rfl

theorem cell23_4930250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_4930250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930250 prefixEnd_4930250 := by exact prefixLift 4930250
  have htrace : WordTrace (prefixWord ++ tailWord_4930250) baseStart_4930250 baseEnd_4930250 := by
    simpa [prefixWord, tailWord_4930250, baseEnd_4930250] using wordTrace_append hprefix tailTrace_4930250
  have hstable : (prefixWord ++ tailWord_4930250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930250).length < 2 ^ (prefixWord ++ tailWord_4930250).sum := by decide
  have hdescent : baseEnd_4930250 < baseStart_4930250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930287 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 3]
def baseStart_4930287 : Nat := 118140960795 + 4930287 * 2 ^ 59
def prefixEnd_4930287 : Nat := 4983230072969 + 3 ^ 40 * 4930287 * 2
def baseEnd_4930287 : Nat := 2531606995613656963138529

theorem tailTrace_4930287 : CollatzResearch.WordTrace tailWord_4930287 prefixEnd_4930287 2531606995613656963138529 := by
  unfold tailWord_4930287
  simp only [CollatzResearch.WordTrace]
  refine ⟨179822339889419699827597115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119881559926279799885064743 179822339889419699827597115)
  ·
    refine ⟨269733509834129549741395673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179822339889419699827597115 269733509834129549741395673)
    ·
      refine ⟨202300132375597162306046755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269733509834129549741395673 202300132375597162306046755)
      ·
        refine ⟨303450198563395743459070133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202300132375597162306046755 303450198563395743459070133)
        ·
          refine ⟨28448456115318350949287825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 303450198563395743459070133 28448456115318350949287825)
          ·
            refine ⟨21336342086488763211965869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28448456115318350949287825 21336342086488763211965869)
            ·
              refine ⟨8001128282433286204487201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21336342086488763211965869 8001128282433286204487201)
              ·
                refine ⟨6000846211824964653365401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8001128282433286204487201 6000846211824964653365401)
                ·
                  refine ⟨4500634658868723490024051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000846211824964653365401 4500634658868723490024051)
                  ·
                    refine ⟨6750951988303085235036077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500634658868723490024051 6750951988303085235036077)
                    ·
                      refine ⟨2531606995613656963138529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750951988303085235036077 2531606995613656963138529)
                      ·
                        rfl

theorem cell23_4930287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_4930287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930287 prefixEnd_4930287 := by exact prefixLift 4930287
  have htrace : WordTrace (prefixWord ++ tailWord_4930287) baseStart_4930287 baseEnd_4930287 := by
    simpa [prefixWord, tailWord_4930287, baseEnd_4930287] using wordTrace_append hprefix tailTrace_4930287
  have hstable : (prefixWord ++ tailWord_4930287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930287).length < 2 ^ (prefixWord ++ tailWord_4930287).sum := by decide
  have hdescent : baseEnd_4930287 < baseStart_4930287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930313 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_4930313 : Nat := 118140960795 + 4930313 * 2 ^ 59
def prefixEnd_4930313 : Nat := 4983230072969 + 3 ^ 40 * 4930313 * 2
def baseEnd_4930313 : Nat := 2531620346110673861413409

theorem tailTrace_4930313 : CollatzResearch.WordTrace tailWord_4930313 prefixEnd_4930313 2531620346110673861413409 := by
  unfold tailWord_4930313
  simp only [CollatzResearch.WordTrace]
  refine ⟨179823288187325506268043593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119882192124883670845362395 179823288187325506268043593)
  ·
    refine ⟨134867466140494129701032695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179823288187325506268043593 134867466140494129701032695)
    ·
      refine ⟨202301199210741194551549043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134867466140494129701032695 202301199210741194551549043)
      ·
        refine ⟨303451798816111791827323565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202301199210741194551549043 303451798816111791827323565)
        ·
          refine ⟨113794424556041921935246337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303451798816111791827323565 113794424556041921935246337)
          ·
            refine ⟨85345818417031441451434753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113794424556041921935246337 85345818417031441451434753)
            ·
              refine ⟨64009363812773581088576065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85345818417031441451434753 64009363812773581088576065)
              ·
                refine ⟨48007022859580185816432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64009363812773581088576065 48007022859580185816432049)
                ·
                  refine ⟨36005267144685139362324037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48007022859580185816432049 36005267144685139362324037)
                  ·
                    refine ⟨6750987589628463630435757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36005267144685139362324037 6750987589628463630435757)
                    ·
                      refine ⟨2531620346110673861413409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6750987589628463630435757 2531620346110673861413409)
                      ·
                        rfl

theorem cell23_4930313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_4930313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930313 prefixEnd_4930313 := by exact prefixLift 4930313
  have htrace : WordTrace (prefixWord ++ tailWord_4930313) baseStart_4930313 baseEnd_4930313 := by
    simpa [prefixWord, tailWord_4930313, baseEnd_4930313] using wordTrace_append hprefix tailTrace_4930313
  have hstable : (prefixWord ++ tailWord_4930313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930313).length < 2 ^ (prefixWord ++ tailWord_4930313).sum := by decide
  have hdescent : baseEnd_4930313 < baseStart_4930313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930344 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4930344 : Nat := 118140960795 + 4930344 * 2 ^ 59
def prefixEnd_4930344 : Nat := 4983230072969 + 3 ^ 40 * 4930344 * 2
def baseEnd_4930344 : Nat := 2531636264010963240125767

theorem tailTrace_4930344 : CollatzResearch.WordTrace tailWord_4930344 prefixEnd_4930344 2531636264010963240125767 := by
  unfold tailWord_4930344
  simp only [CollatzResearch.WordTrace]
  refine ⟨89912209425106599281211043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119882945900142132374948057 89912209425106599281211043)
  ·
    refine ⟨134868314137659898921816565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89912209425106599281211043 134868314137659898921816565)
    ·
      refine ⟨12643904450405615523920303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134868314137659898921816565 12643904450405615523920303)
      ·
        refine ⟨18965856675608423285880455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12643904450405615523920303 18965856675608423285880455)
        ·
          refine ⟨28448785013412634928820683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18965856675608423285880455 28448785013412634928820683)
          ·
            refine ⟨42673177520118952393231025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28448785013412634928820683 42673177520118952393231025)
            ·
              refine ⟨32004883140089214294923269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42673177520118952393231025 32004883140089214294923269)
              ·
                refine ⟨6000915588766727680298113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32004883140089214294923269 6000915588766727680298113)
                ·
                  refine ⟨4500686691575045760223585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000915588766727680298113 4500686691575045760223585)
                  ·
                    refine ⟨3375515018681284320167689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4500686691575045760223585 3375515018681284320167689)
                    ·
                      refine ⟨2531636264010963240125767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375515018681284320167689 2531636264010963240125767)
                      ·
                        rfl

theorem cell23_4930344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4930344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930344 prefixEnd_4930344 := by exact prefixLift 4930344
  have htrace : WordTrace (prefixWord ++ tailWord_4930344) baseStart_4930344 baseEnd_4930344 := by
    simpa [prefixWord, tailWord_4930344, baseEnd_4930344] using wordTrace_append hprefix tailTrace_4930344
  have hstable : (prefixWord ++ tailWord_4930344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930344).length < 2 ^ (prefixWord ++ tailWord_4930344).sum := by decide
  have hdescent : baseEnd_4930344 < baseStart_4930344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930380 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_4930380 : Nat := 118140960795 + 4930380 * 2 ^ 59
def prefixEnd_4930380 : Nat := 4983230072969 + 3 ^ 40 * 4930380 * 2
def baseEnd_4930380 : Nat := 843884916438175033091867

theorem tailTrace_4930380 : CollatzResearch.WordTrace tailWord_4930380 prefixEnd_4930380 843884916438175033091867 := by
  unfold tailWord_4930380
  simp only [CollatzResearch.WordTrace]
  refine ⟨89912865939041388355366297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119883821252055184473821729 89912865939041388355366297)
  ·
    refine ⟨67434649454281041266524723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89912865939041388355366297 67434649454281041266524723)
    ·
      refine ⟨101151974181421561899787085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67434649454281041266524723 101151974181421561899787085)
      ·
        refine ⟨37931990318033085712420157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101151974181421561899787085 37931990318033085712420157)
        ·
          refine ⟨14224496369262407142157559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37931990318033085712420157 14224496369262407142157559)
          ·
            refine ⟨21336744553893610713236339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14224496369262407142157559 21336744553893610713236339)
            ·
              refine ⟨32005116830840416069854509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21336744553893610713236339 32005116830840416069854509)
              ·
                refine ⟨12001918811565156026195441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32005116830840416069854509 12001918811565156026195441)
                ·
                  refine ⟨9001439108673867019646581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12001918811565156026195441 9001439108673867019646581)
                  ·
                    refine ⟨843884916438175033091867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9001439108673867019646581 843884916438175033091867)
                    ·
                      rfl

theorem cell23_4930380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_4930380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930380 prefixEnd_4930380 := by exact prefixLift 4930380
  have htrace : WordTrace (prefixWord ++ tailWord_4930380) baseStart_4930380 baseEnd_4930380 := by
    simpa [prefixWord, tailWord_4930380, baseEnd_4930380] using wordTrace_append hprefix tailTrace_4930380
  have hstable : (prefixWord ++ tailWord_4930380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930380).length < 2 ^ (prefixWord ++ tailWord_4930380).sum := by decide
  have hdescent : baseEnd_4930380 < baseStart_4930380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930400 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_4930400 : Nat := 118140960795 + 4930400 * 2 ^ 59
def prefixEnd_4930400 : Nat := 4983230072969 + 3 ^ 40 * 4930400 * 2
def baseEnd_4930400 : Nat := 2531665018927615021025509

theorem tailTrace_4930400 : CollatzResearch.WordTrace tailWord_4930400 prefixEnd_4930400 2531665018927615021025509 := by
  unfold tailWord_4930400
  simp only [CollatzResearch.WordTrace]
  refine ⟨89913230669005160063230327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119884307558673546750973769 89913230669005160063230327)
  ·
    refine ⟨134869846003507740094845491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89913230669005160063230327 134869846003507740094845491)
    ·
      refine ⟨202304769005261610142268237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134869846003507740094845491 202304769005261610142268237)
      ·
        refine ⟨75864288376973103803350589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202304769005261610142268237 75864288376973103803350589)
        ·
          refine ⟨28449108141364913926256471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75864288376973103803350589 28449108141364913926256471)
          ·
            refine ⟨42673662212047370889384707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28449108141364913926256471 42673662212047370889384707)
            ·
              refine ⟨64010493318071056334077061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42673662212047370889384707 64010493318071056334077061)
              ·
                refine ⟨12001967497138323062639449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64010493318071056334077061 12001967497138323062639449)
                ·
                  refine ⟨9001475622853742296979587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12001967497138323062639449 9001475622853742296979587)
                  ·
                    refine ⟨13502213434280613445469381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9001475622853742296979587 13502213434280613445469381)
                    ·
                      refine ⟨2531665018927615021025509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13502213434280613445469381 2531665018927615021025509)
                      ·
                        rfl

theorem cell23_4930400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_4930400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930400 prefixEnd_4930400 := by exact prefixLift 4930400
  have htrace : WordTrace (prefixWord ++ tailWord_4930400) baseStart_4930400 baseEnd_4930400 := by
    simpa [prefixWord, tailWord_4930400, baseEnd_4930400] using wordTrace_append hprefix tailTrace_4930400
  have hstable : (prefixWord ++ tailWord_4930400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930400).length < 2 ^ (prefixWord ++ tailWord_4930400).sum := by decide
  have hdescent : baseEnd_4930400 < baseStart_4930400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930417 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_4930417 : Nat := 118140960795 + 4930417 * 2 ^ 59
def prefixEnd_4930417 : Nat := 4983230072969 + 3 ^ 40 * 4930417 * 2
def baseEnd_4930417 : Nat := 2531673748098741454512931

theorem tailTrace_4930417 : CollatzResearch.WordTrace tailWord_4930417 prefixEnd_4930417 2531673748098741454512931 := by
  unfold tailWord_4930417
  simp only [CollatzResearch.WordTrace]
  refine ⟨179827081378948732029829505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119884720919299154686553003 179827081378948732029829505)
  ·
    refine ⟨134870311034211549022372129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179827081378948732029829505 134870311034211549022372129)
    ·
      refine ⟨101152733275658661766779097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134870311034211549022372129 101152733275658661766779097)
      ·
        refine ⟨75864549956743996325084323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101152733275658661766779097 75864549956743996325084323)
        ·
          refine ⟨113796824935115994487626485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75864549956743996325084323 113796824935115994487626485)
          ·
            refine ⟨10668452337667124483214983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113796824935115994487626485 10668452337667124483214983)
            ·
              refine ⟨16002678506500686724822475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10668452337667124483214983 16002678506500686724822475)
              ·
                refine ⟨24004017759751030087233713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16002678506500686724822475 24004017759751030087233713)
                ·
                  refine ⟨18003013319813272565425285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24004017759751030087233713 18003013319813272565425285)
                  ·
                    refine ⟨3375564997464988606017241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18003013319813272565425285 3375564997464988606017241)
                    ·
                      refine ⟨2531673748098741454512931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375564997464988606017241 2531673748098741454512931)
                      ·
                        rfl

theorem cell23_4930417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_4930417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930417 prefixEnd_4930417 := by exact prefixLift 4930417
  have htrace : WordTrace (prefixWord ++ tailWord_4930417) baseStart_4930417 baseEnd_4930417 := by
    simpa [prefixWord, tailWord_4930417, baseEnd_4930417] using wordTrace_append hprefix tailTrace_4930417
  have hstable : (prefixWord ++ tailWord_4930417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930417).length < 2 ^ (prefixWord ++ tailWord_4930417).sum := by decide
  have hdescent : baseEnd_4930417 < baseStart_4930417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930437 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_4930437 : Nat := 118140960795 + 4930437 * 2 ^ 59
def prefixEnd_4930437 : Nat := 4983230072969 + 3 ^ 40 * 4930437 * 2
def baseEnd_4930437 : Nat := 2531684017711831376262839

theorem tailTrace_4930437 : CollatzResearch.WordTrace tailWord_4930437 prefixEnd_4930437 2531684017711831376262839 := by
  unfold tailWord_4930437
  simp only [CollatzResearch.WordTrace]
  refine ⟨179827810838876275445557565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119885207225917516963705043 179827810838876275445557565)
  ·
    refine ⟨67435429064578603292084087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179827810838876275445557565 67435429064578603292084087)
    ·
      refine ⟨101153143596867904938126131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67435429064578603292084087 101153143596867904938126131)
      ·
        refine ⟨151729715395301857407189197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101153143596867904938126131 151729715395301857407189197)
        ·
          refine ⟨56898643273238196527695949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151729715395301857407189197 56898643273238196527695949)
          ·
            refine ⟨21336991227464323697885981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56898643273238196527695949 21336991227464323697885981)
            ·
              refine ⟨8001371710299121386707243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21336991227464323697885981 8001371710299121386707243)
              ·
                refine ⟨12002057565448682080060865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8001371710299121386707243 12002057565448682080060865)
                ·
                  refine ⟨9001543174086511560045649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12002057565448682080060865 9001543174086511560045649)
                  ·
                    refine ⟨6751157380564883670034237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9001543174086511560045649 6751157380564883670034237)
                    ·
                      refine ⟨2531684017711831376262839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751157380564883670034237 2531684017711831376262839)
                      ·
                        rfl

theorem cell23_4930437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_4930437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930437 prefixEnd_4930437 := by exact prefixLift 4930437
  have htrace : WordTrace (prefixWord ++ tailWord_4930437) baseStart_4930437 baseEnd_4930437 := by
    simpa [prefixWord, tailWord_4930437, baseEnd_4930437] using wordTrace_append hprefix tailTrace_4930437
  have hstable : (prefixWord ++ tailWord_4930437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930437).length < 2 ^ (prefixWord ++ tailWord_4930437).sum := by decide
  have hdescent : baseEnd_4930437 < baseStart_4930437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930467 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 3]
def baseStart_4930467 : Nat := 118140960795 + 4930467 * 2 ^ 59
def prefixEnd_4930467 : Nat := 4983230072969 + 3 ^ 40 * 4930467 * 2
def baseEnd_4930467 : Nat := 2531699422131466258887701

theorem tailTrace_4930467 : CollatzResearch.WordTrace tailWord_4930467 prefixEnd_4930467 2531699422131466258887701 := by
  unfold tailWord_4930467
  simp only [CollatzResearch.WordTrace]
  refine ⟨179828905028767590569149655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119885936685845060379433103 179828905028767590569149655)
  ·
    refine ⟨269743357543151385853724483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179828905028767590569149655 269743357543151385853724483)
    ·
      refine ⟨404615036314727078780586725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269743357543151385853724483 404615036314727078780586725)
      ·
        refine ⟨75865319309011327271360011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 404615036314727078780586725 75865319309011327271360011)
        ·
          refine ⟨113797978963516990907040017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75865319309011327271360011 113797978963516990907040017)
          ·
            refine ⟨85348484222637743180280013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113797978963516990907040017 85348484222637743180280013)
            ·
              refine ⟨32005681583489153692605005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85348484222637743180280013 32005681583489153692605005)
              ·
                refine ⟨12002130593808432634726877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32005681583489153692605005 12002130593808432634726877)
                ·
                  refine ⟨4500798972678162238022579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12002130593808432634726877 4500798972678162238022579)
                  ·
                    refine ⟨6751198459017243357033869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500798972678162238022579 6751198459017243357033869)
                    ·
                      refine ⟨2531699422131466258887701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751198459017243357033869 2531699422131466258887701)
                      ·
                        rfl

theorem cell23_4930467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_4930467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930467 prefixEnd_4930467 := by exact prefixLift 4930467
  have htrace : WordTrace (prefixWord ++ tailWord_4930467) baseStart_4930467 baseEnd_4930467 := by
    simpa [prefixWord, tailWord_4930467, baseEnd_4930467] using wordTrace_append hprefix tailTrace_4930467
  have hstable : (prefixWord ++ tailWord_4930467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930467).length < 2 ^ (prefixWord ++ tailWord_4930467).sum := by decide
  have hdescent : baseEnd_4930467 < baseStart_4930467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930494 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_4930494 : Nat := 118140960795 + 4930494 * 2 ^ 59
def prefixEnd_4930494 : Nat := 4983230072969 + 3 ^ 40 * 4930494 * 2
def baseEnd_4930494 : Nat := 2531713286109137653250077

theorem tailTrace_4930494 : CollatzResearch.WordTrace tailWord_4930494 prefixEnd_4930494 2531713286109137653250077 := by
  unfold tailWord_4930494
  simp only [CollatzResearch.WordTrace]
  refine ⟨22478736224958721772547817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119886593199779849453588357 22478736224958721772547817)
  ·
    refine ⟨16859052168719041329410863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22478736224958721772547817 16859052168719041329410863)
    ·
      refine ⟨25288578253078561994116295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16859052168719041329410863 25288578253078561994116295)
      ·
        refine ⟨37932867379617842991174443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25288578253078561994116295 37932867379617842991174443)
        ·
          refine ⟨56899301069426764486761665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37932867379617842991174443 56899301069426764486761665)
          ·
            refine ⟨42674475802070073365071249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56899301069426764486761665 42674475802070073365071249)
            ·
              refine ⟨32005856851552555023803437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42674475802070073365071249 32005856851552555023803437)
              ·
                refine ⟨12002196319332208133926289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32005856851552555023803437 12002196319332208133926289)
                ·
                  refine ⟨9001647239499156100444717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12002196319332208133926289 9001647239499156100444717)
                  ·
                    refine ⟨3375617714812183537666769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9001647239499156100444717 3375617714812183537666769)
                    ·
                      refine ⟨2531713286109137653250077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375617714812183537666769 2531713286109137653250077)
                      ·
                        rfl

theorem cell23_4930494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_4930494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930494 prefixEnd_4930494 := by exact prefixLift 4930494
  have htrace : WordTrace (prefixWord ++ tailWord_4930494) baseStart_4930494 baseEnd_4930494 := by
    simpa [prefixWord, tailWord_4930494, baseEnd_4930494] using wordTrace_append hprefix tailTrace_4930494
  have hstable : (prefixWord ++ tailWord_4930494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930494).length < 2 ^ (prefixWord ++ tailWord_4930494).sum := by decide
  have hdescent : baseEnd_4930494 < baseStart_4930494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930507 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 4]
def baseStart_4930507 : Nat := 118140960795 + 4930507 * 2 ^ 59
def prefixEnd_4930507 : Nat := 4983230072969 + 3 ^ 40 * 4930507 * 2
def baseEnd_4930507 : Nat := 2531719961357646102387517

theorem tailTrace_4930507 : CollatzResearch.WordTrace tailWord_4930507 prefixEnd_4930507 2531719961357646102387517 := by
  unfold tailWord_4930507
  simp only [CollatzResearch.WordTrace]
  refine ⟨179830363948622677400605775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119886909299081784933737183 179830363948622677400605775)
  ·
    refine ⟨269745545922934016100908663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179830363948622677400605775 269745545922934016100908663)
    ·
      refine ⟨404618318884401024151362995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269745545922934016100908663 404618318884401024151362995)
      ·
        refine ⟨606927478326601536227044493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404618318884401024151362995 606927478326601536227044493)
        ·
          refine ⟨227597804372475576085141685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606927478326601536227044493 227597804372475576085141685)
          ·
            refine ⟨21337294159919585257982033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227597804372475576085141685 21337294159919585257982033)
            ·
              refine ⟨16002970619939688943486525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21337294159919585257982033 16002970619939688943486525)
              ·
                refine ⟨6001113982477383353807447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16002970619939688943486525 6001113982477383353807447)
                ·
                  refine ⟨9001670973716075030711171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6001113982477383353807447 9001670973716075030711171)
                  ·
                    refine ⟨13502506460574112546066757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9001670973716075030711171 13502506460574112546066757)
                    ·
                      refine ⟨2531719961357646102387517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13502506460574112546066757 2531719961357646102387517)
                      ·
                        rfl

theorem cell23_4930507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 4].length) (baseStart_4930507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930507 prefixEnd_4930507 := by exact prefixLift 4930507
  have htrace : WordTrace (prefixWord ++ tailWord_4930507) baseStart_4930507 baseEnd_4930507 := by
    simpa [prefixWord, tailWord_4930507, baseEnd_4930507] using wordTrace_append hprefix tailTrace_4930507
  have hstable : (prefixWord ++ tailWord_4930507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930507).length < 2 ^ (prefixWord ++ tailWord_4930507).sum := by decide
  have hdescent : baseEnd_4930507 < baseStart_4930507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930518 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4930518 : Nat := 118140960795 + 4930518 * 2 ^ 59
def prefixEnd_4930518 : Nat := 4983230072969 + 3 ^ 40 * 4930518 * 2
def baseEnd_4930518 : Nat := 2531725609644845559349967

theorem tailTrace_4930518 : CollatzResearch.WordTrace tailWord_4930518 prefixEnd_4930518 2531725609644845559349967 := by
  unfold tailWord_4930518
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239422821973926642453513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119887176767721884186170805 11239422821973926642453513)
  ·
    refine ⟨8429567116480444981840135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11239422821973926642453513 8429567116480444981840135)
    ·
      refine ⟨12644350674720667472760203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8429567116480444981840135 12644350674720667472760203)
      ·
        refine ⟨18966526012081001209140305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12644350674720667472760203 18966526012081001209140305)
        ·
          refine ⟨14224894509060750906855229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18966526012081001209140305 14224894509060750906855229)
          ·
            refine ⟨5334335440897781590070711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14224894509060750906855229 5334335440897781590070711)
            ·
              refine ⟨8001503161346672385106067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5334335440897781590070711 8001503161346672385106067)
              ·
                refine ⟨12002254742020008577659101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8001503161346672385106067 12002254742020008577659101)
                ·
                  refine ⟨4500845528257503216622163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12002254742020008577659101 4500845528257503216622163)
                  ·
                    refine ⟨6751268292386254824933245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500845528257503216622163 6751268292386254824933245)
                    ·
                      refine ⟨2531725609644845559349967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751268292386254824933245 2531725609644845559349967)
                      ·
                        rfl

theorem cell23_4930518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4930518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930518 prefixEnd_4930518 := by exact prefixLift 4930518
  have htrace : WordTrace (prefixWord ++ tailWord_4930518) baseStart_4930518 baseEnd_4930518 := by
    simpa [prefixWord, tailWord_4930518, baseEnd_4930518] using wordTrace_append hprefix tailTrace_4930518
  have hstable : (prefixWord ++ tailWord_4930518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930518).length < 2 ^ (prefixWord ++ tailWord_4930518).sum := by decide
  have hdescent : baseEnd_4930518 < baseStart_4930518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930520 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_4930520 : Nat := 118140960795 + 4930520 * 2 ^ 59
def prefixEnd_4930520 : Nat := 4983230072969 + 3 ^ 40 * 4930520 * 2
def baseEnd_4930520 : Nat := 2531726636606154551524957

theorem tailTrace_4930520 : CollatzResearch.WordTrace tailWord_4930520 prefixEnd_4930520 2531726636606154551524957 := by
  unfold tailWord_4930520
  simp only [CollatzResearch.WordTrace]
  refine ⟨89915419048787790310414507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119887225398383720413886009 89915419048787790310414507)
  ·
    refine ⟨134873128573181685465621761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89915419048787790310414507 134873128573181685465621761)
    ·
      refine ⟨101154846429886264099216321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134873128573181685465621761 101154846429886264099216321)
      ·
        refine ⟨75866134822414698074412241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101154846429886264099216321 75866134822414698074412241)
        ·
          refine ⟨56899601116811023555809181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75866134822414698074412241 56899601116811023555809181)
          ·
            refine ⟨21337350418804133833428443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56899601116811023555809181 21337350418804133833428443)
            ·
              refine ⟨32006025628206200750142665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21337350418804133833428443 32006025628206200750142665)
              ·
                refine ⟨24004519221154650562606999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32006025628206200750142665 24004519221154650562606999)
                ·
                  refine ⟨36006778831731975843910499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24004519221154650562606999 36006778831731975843910499)
                  ·
                    refine ⟨54010168247597963765865749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36006778831731975843910499 54010168247597963765865749)
                    ·
                      refine ⟨2531726636606154551524957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54010168247597963765865749 2531726636606154551524957)
                      ·
                        rfl

theorem cell23_4930520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_4930520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930520 prefixEnd_4930520 := by exact prefixLift 4930520
  have htrace : WordTrace (prefixWord ++ tailWord_4930520) baseStart_4930520 baseEnd_4930520 := by
    simpa [prefixWord, tailWord_4930520, baseEnd_4930520] using wordTrace_append hprefix tailTrace_4930520
  have hstable : (prefixWord ++ tailWord_4930520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930520).length < 2 ^ (prefixWord ++ tailWord_4930520).sum := by decide
  have hdescent : baseEnd_4930520 < baseStart_4930520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930558 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4930558 : Nat := 118140960795 + 4930558 * 2 ^ 59
def prefixEnd_4930558 : Nat := 4983230072969 + 3 ^ 40 * 4930558 * 2
def baseEnd_4930558 : Nat := 2531746148871025402849783

theorem tailTrace_4930558 : CollatzResearch.WordTrace tailWord_4930558 prefixEnd_4930558 2531746148871025402849783 := by
  unfold tailWord_4930558
  simp only [CollatzResearch.WordTrace]
  refine ⟨22479028008929739138839041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119888149380958608740474885 22479028008929739138839041)
  ·
    refine ⟨16859271006697304354129281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22479028008929739138839041 16859271006697304354129281)
    ·
      refine ⟨12644453255022978265596961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16859271006697304354129281 12644453255022978265596961)
      ·
        refine ⟨9483339941267233699197721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12644453255022978265596961 9483339941267233699197721)
        ·
          refine ⟨7112504955950425274398291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9483339941267233699197721 7112504955950425274398291)
          ·
            refine ⟨10668757433925637911597437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7112504955950425274398291 10668757433925637911597437)
            ·
              refine ⟨4000784037722114216849039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10668757433925637911597437 4000784037722114216849039)
              ·
                refine ⟨6001176056583171325273559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000784037722114216849039 6001176056583171325273559)
                ·
                  refine ⟨9001764084874756987910339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6001176056583171325273559 9001764084874756987910339)
                  ·
                    refine ⟨13502646127312135481865509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9001764084874756987910339 13502646127312135481865509)
                    ·
                      refine ⟨2531746148871025402849783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13502646127312135481865509 2531746148871025402849783)
                      ·
                        rfl

theorem cell23_4930558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4930558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930558 prefixEnd_4930558 := by exact prefixLift 4930558
  have htrace : WordTrace (prefixWord ++ tailWord_4930558) baseStart_4930558 baseEnd_4930558 := by
    simpa [prefixWord, tailWord_4930558, baseEnd_4930558] using wordTrace_append hprefix tailTrace_4930558
  have hstable : (prefixWord ++ tailWord_4930558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930558).length < 2 ^ (prefixWord ++ tailWord_4930558).sum := by decide
  have hdescent : baseEnd_4930558 < baseStart_4930558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930561 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_4930561 : Nat := 118140960795 + 4930561 * 2 ^ 59
def prefixEnd_4930561 : Nat := 4983230072969 + 3 ^ 40 * 4930561 * 2
def baseEnd_4930561 : Nat := 2531747689312988891112269

theorem tailTrace_4930561 : CollatzResearch.WordTrace tailWord_4930561 prefixEnd_4930561 2531747689312988891112269 := by
  unfold tailWord_4930561
  simp only [CollatzResearch.WordTrace]
  refine ⟨179832333490427044623071537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119888222326951363082047691 179832333490427044623071537)
  ·
    refine ⟨134874250117820283467303653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179832333490427044623071537 134874250117820283467303653)
    ·
      refine ⟨25288921897091303150119435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134874250117820283467303653 25288921897091303150119435)
      ·
        refine ⟨37933382845636954725179153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25288921897091303150119435 37933382845636954725179153)
        ·
          refine ⟨28450037134227716043884365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37933382845636954725179153 28450037134227716043884365)
          ·
            refine ⟨10668763925335393516456637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28450037134227716043884365 10668763925335393516456637)
            ·
              refine ⟨4000786472000772568671239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10668763925335393516456637 4000786472000772568671239)
              ·
                refine ⟨6001179708001158853006859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000786472000772568671239 6001179708001158853006859)
                ·
                  refine ⟨9001769562001738279510289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6001179708001158853006859 9001769562001738279510289)
                  ·
                    refine ⟨6751327171501303709632717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9001769562001738279510289 6751327171501303709632717)
                    ·
                      refine ⟨2531747689312988891112269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751327171501303709632717 2531747689312988891112269)
                      ·
                        rfl

theorem cell23_4930561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_4930561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930561 prefixEnd_4930561 := by exact prefixLift 4930561
  have htrace : WordTrace (prefixWord ++ tailWord_4930561) baseStart_4930561 baseEnd_4930561 := by
    simpa [prefixWord, tailWord_4930561, baseEnd_4930561] using wordTrace_append hprefix tailTrace_4930561
  have hstable : (prefixWord ++ tailWord_4930561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930561).length < 2 ^ (prefixWord ++ tailWord_4930561).sum := by decide
  have hdescent : baseEnd_4930561 < baseStart_4930561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930584 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_4930584 : Nat := 118140960795 + 4930584 * 2 ^ 59
def prefixEnd_4930584 : Nat := 4983230072969 + 3 ^ 40 * 4930584 * 2
def baseEnd_4930584 : Nat := 2531759499368042301124663

theorem tailTrace_4930584 : CollatzResearch.WordTrace tailWord_4930584 prefixEnd_4930584 2531759499368042301124663 := by
  unfold tailWord_4930584
  simp only [CollatzResearch.WordTrace]
  refine ⟨89916586184671859775579403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119888781579562479700772537 89916586184671859775579403)
  ·
    refine ⟨134874879277007789663369105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89916586184671859775579403 134874879277007789663369105)
    ·
      refine ⟨101156159457755842247526829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134874879277007789663369105 101156159457755842247526829)
      ·
        refine ⟨37933559796658440842822561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101156159457755842247526829 37933559796658440842822561)
        ·
          refine ⟨28450169847493830632116921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37933559796658440842822561 28450169847493830632116921)
          ·
            refine ⟨21337627385620372974087691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28450169847493830632116921 21337627385620372974087691)
            ·
              refine ⟨32006441078430559461131537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21337627385620372974087691 32006441078430559461131537)
              ·
                refine ⟨24004830808822919595848653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32006441078430559461131537 24004830808822919595848653)
                ·
                  refine ⟨9001811553308594848443245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24004830808822919595848653 9001811553308594848443245)
                  ·
                    refine ⟨3375679332490723068166217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9001811553308594848443245 3375679332490723068166217)
                    ·
                      refine ⟨2531759499368042301124663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375679332490723068166217 2531759499368042301124663)
                      ·
                        rfl

theorem cell23_4930584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_4930584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930584 prefixEnd_4930584 := by exact prefixLift 4930584
  have htrace : WordTrace (prefixWord ++ tailWord_4930584) baseStart_4930584 baseEnd_4930584 := by
    simpa [prefixWord, tailWord_4930584, baseEnd_4930584] using wordTrace_append hprefix tailTrace_4930584
  have hstable : (prefixWord ++ tailWord_4930584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930584).length < 2 ^ (prefixWord ++ tailWord_4930584).sum := by decide
  have hdescent : baseEnd_4930584 < baseStart_4930584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930625 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_4930625 : Nat := 118140960795 + 4930625 * 2 ^ 59
def prefixEnd_4930625 : Nat := 4983230072969 + 3 ^ 40 * 4930625 * 2
def baseEnd_4930625 : Nat := 2531780552074876640711975

theorem tailTrace_4930625 : CollatzResearch.WordTrace tailWord_4930625 prefixEnd_4930625 2531780552074876640711975 := by
  unfold tailWord_4930625
  simp only [CollatzResearch.WordTrace]
  refine ⟨179834667762195183553401329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119889778508130122368934219 179834667762195183553401329)
  ·
    refine ⟨134876000821646387665050997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179834667762195183553401329 134876000821646387665050997)
    ·
      refine ⟨12644625077029348843598531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134876000821646387665050997 12644625077029348843598531)
      ·
        refine ⟨18966937615544023265397797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12644625077029348843598531 18966937615544023265397797)
        ·
          refine ⟨3556300802914504362262087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18966937615544023265397797 3556300802914504362262087)
          ·
            refine ⟨5334451204371756543393131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556300802914504362262087 5334451204371756543393131)
            ·
              refine ⟨8001676806557634815089697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5334451204371756543393131 8001676806557634815089697)
              ·
                refine ⟨6001257604918226111317273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8001676806557634815089697 6001257604918226111317273)
                ·
                  refine ⟨4500943203688669583487955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6001257604918226111317273 4500943203688669583487955)
                  ·
                    refine ⟨6751414805533004375231933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4500943203688669583487955 6751414805533004375231933)
                    ·
                      refine ⟨2531780552074876640711975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751414805533004375231933 2531780552074876640711975)
                      ·
                        rfl

theorem cell23_4930625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_4930625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930625 prefixEnd_4930625 := by exact prefixLift 4930625
  have htrace : WordTrace (prefixWord ++ tailWord_4930625) baseStart_4930625 baseEnd_4930625 := by
    simpa [prefixWord, tailWord_4930625, baseEnd_4930625] using wordTrace_append hprefix tailTrace_4930625
  have hstable : (prefixWord ++ tailWord_4930625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930625).length < 2 ^ (prefixWord ++ tailWord_4930625).sum := by decide
  have hdescent : baseEnd_4930625 < baseStart_4930625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930631 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_4930631 : Nat := 118140960795 + 4930631 * 2 ^ 59
def prefixEnd_4930631 : Nat := 4983230072969 + 3 ^ 40 * 4930631 * 2
def baseEnd_4930631 : Nat := 2531783632958803617236947

theorem tailTrace_4930631 : CollatzResearch.WordTrace tailWord_4930631 prefixEnd_4930631 2531783632958803617236947 := by
  unfold tailWord_4930631
  simp only [CollatzResearch.WordTrace]
  refine ⟨179834886600173446578119747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119889924400115631052079831 179834886600173446578119747)
  ·
    refine ⟨269752329900260169867179621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179834886600173446578119747 269752329900260169867179621)
    ·
      refine ⟨50578561856298781850096179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269752329900260169867179621 50578561856298781850096179)
      ·
        refine ⟨75867842784448172775144269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50578561856298781850096179 75867842784448172775144269)
        ·
          refine ⟨28450441044168064790679101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75867842784448172775144269 28450441044168064790679101)
          ·
            refine ⟨10668915391563024296504663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28450441044168064790679101 10668915391563024296504663)
            ·
              refine ⟨16003373087344536444756995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10668915391563024296504663 16003373087344536444756995)
              ·
                refine ⟨24005059631016804667135493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16003373087344536444756995 24005059631016804667135493)
                ·
                  refine ⟨4500948680815650875087905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24005059631016804667135493 4500948680815650875087905)
                  ·
                    refine ⟨3375711510611738156315929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4500948680815650875087905 3375711510611738156315929)
                    ·
                      refine ⟨2531783632958803617236947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375711510611738156315929 2531783632958803617236947)
                      ·
                        rfl

theorem cell23_4930631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_4930631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930631 prefixEnd_4930631 := by exact prefixLift 4930631
  have htrace : WordTrace (prefixWord ++ tailWord_4930631) baseStart_4930631 baseEnd_4930631 := by
    simpa [prefixWord, tailWord_4930631, baseEnd_4930631] using wordTrace_append hprefix tailTrace_4930631
  have hstable : (prefixWord ++ tailWord_4930631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930631).length < 2 ^ (prefixWord ++ tailWord_4930631).sum := by decide
  have hdescent : baseEnd_4930631 < baseStart_4930631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930648 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_4930648 : Nat := 118140960795 + 4930648 * 2 ^ 59
def prefixEnd_4930648 : Nat := 4983230072969 + 3 ^ 40 * 4930648 * 2
def baseEnd_4930648 : Nat := 2531792362129930050724369

theorem tailTrace_4930648 : CollatzResearch.WordTrace tailWord_4930648 prefixEnd_4930648 2531792362129930050724369 := by
  unfold tailWord_4930648
  simp only [CollatzResearch.WordTrace]
  refine ⟨89917753320555929240744299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119890337760741238987659065 89917753320555929240744299)
  ·
    refine ⟨134876629980833893861116449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89917753320555929240744299 134876629980833893861116449)
    ·
      refine ⟨101157472485625420395837337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134876629980833893861116449 101157472485625420395837337)
      ·
        refine ⟨75868104364219065296878003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101157472485625420395837337 75868104364219065296878003)
        ·
          refine ⟨113802156546328597945317005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75868104364219065296878003 113802156546328597945317005)
          ·
            refine ⟨42675808704873224229493877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113802156546328597945317005 42675808704873224229493877)
            ·
              refine ⟨4000857066081864771515051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42675808704873224229493877 4000857066081864771515051)
              ·
                refine ⟨6001285599122797157272577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4000857066081864771515051 6001285599122797157272577)
                ·
                  refine ⟨4500964199342097867954433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6001285599122797157272577 4500964199342097867954433)
                  ·
                    refine ⟨3375723149506573400965825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4500964199342097867954433 3375723149506573400965825)
                    ·
                      refine ⟨2531792362129930050724369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375723149506573400965825 2531792362129930050724369)
                      ·
                        rfl

theorem cell23_4930648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_4930648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930648 prefixEnd_4930648 := by exact prefixLift 4930648
  have htrace : WordTrace (prefixWord ++ tailWord_4930648) baseStart_4930648 baseEnd_4930648 := by
    simpa [prefixWord, tailWord_4930648, baseEnd_4930648] using wordTrace_append hprefix tailTrace_4930648
  have hstable : (prefixWord ++ tailWord_4930648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930648).length < 2 ^ (prefixWord ++ tailWord_4930648).sum := by decide
  have hdescent : baseEnd_4930648 < baseStart_4930648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930707 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3]
def baseStart_4930707 : Nat := 118140960795 + 4930707 * 2 ^ 59
def prefixEnd_4930707 : Nat := 4983230072969 + 3 ^ 40 * 4930707 * 2
def baseEnd_4930707 : Nat := 2531822657488545319886597

theorem tailTrace_4930707 : CollatzResearch.WordTrace tailWord_4930707 prefixEnd_4930707 2531822657488545319886597 := by
  unfold tailWord_4930707
  simp only [CollatzResearch.WordTrace]
  refine ⟨179837658547898111557886375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119891772365265407705257583 179837658547898111557886375)
  ·
    refine ⟨269756487821847167336829563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179837658547898111557886375 269756487821847167336829563)
    ·
      refine ⟨404634731732770751005244345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269756487821847167336829563 404634731732770751005244345)
      ·
        refine ⟨303476048799578063253933259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404634731732770751005244345 303476048799578063253933259)
        ·
          refine ⟨455214073199367094880899889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303476048799578063253933259 455214073199367094880899889)
          ·
            refine ⟨341410554899525321160674917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455214073199367094880899889 341410554899525321160674917)
            ·
              refine ⟨64014479043660997717626547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341410554899525321160674917 64014479043660997717626547)
              ·
                refine ⟨96021718565491496576439821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64014479043660997717626547 96021718565491496576439821)
                ·
                  refine ⟨36008144462059311216164933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96021718565491496576439821 36008144462059311216164933)
                  ·
                    refine ⟨6751527086636120853030925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36008144462059311216164933 6751527086636120853030925)
                    ·
                      refine ⟨2531822657488545319886597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751527086636120853030925 2531822657488545319886597)
                      ·
                        rfl

theorem cell23_4930707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_4930707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930707 prefixEnd_4930707 := by exact prefixLift 4930707
  have htrace : WordTrace (prefixWord ++ tailWord_4930707) baseStart_4930707 baseEnd_4930707 := by
    simpa [prefixWord, tailWord_4930707, baseEnd_4930707] using wordTrace_append hprefix tailTrace_4930707
  have hstable : (prefixWord ++ tailWord_4930707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930707).length < 2 ^ (prefixWord ++ tailWord_4930707).sum := by decide
  have hdescent : baseEnd_4930707 < baseStart_4930707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930748 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_4930748 : Nat := 118140960795 + 4930748 * 2 ^ 59
def prefixEnd_4930748 : Nat := 4983230072969 + 3 ^ 40 * 4930748 * 2
def baseEnd_4930748 : Nat := 843947903398459886491303

theorem tailTrace_4930748 : CollatzResearch.WordTrace tailWord_4930748 prefixEnd_4930748 843947903398459886491303 := by
  unfold tailWord_4930748
  simp only [CollatzResearch.WordTrace]
  refine ⟨89919576970374787780064449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119892769293833050373419265 89919576970374787780064449)
  ·
    refine ⟨67439682727781090835048337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89919576970374787780064449 67439682727781090835048337)
    ·
      refine ⟨50579762045835818126286253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67439682727781090835048337 50579762045835818126286253)
      ·
        refine ⟨18967410767188431797357345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50579762045835818126286253 18967410767188431797357345)
        ·
          refine ⟨14225558075391323848018009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18967410767188431797357345 14225558075391323848018009)
          ·
            refine ⟨10669168556543492886013507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14225558075391323848018009 10669168556543492886013507)
            ·
              refine ⟨16003752834815239329020261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10669168556543492886013507 16003752834815239329020261)
              ·
                refine ⟨3000703656527857374191299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16003752834815239329020261 3000703656527857374191299)
                ·
                  refine ⟨4501055484791786061286949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000703656527857374191299 4501055484791786061286949)
                  ·
                    refine ⟨843947903398459886491303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501055484791786061286949 843947903398459886491303)
                    ·
                      rfl

theorem cell23_4930748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_4930748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930748 prefixEnd_4930748 := by exact prefixLift 4930748
  have htrace : WordTrace (prefixWord ++ tailWord_4930748) baseStart_4930748 baseEnd_4930748 := by
    simpa [prefixWord, tailWord_4930748, baseEnd_4930748] using wordTrace_append hprefix tailTrace_4930748
  have hstable : (prefixWord ++ tailWord_4930748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930748).length < 2 ^ (prefixWord ++ tailWord_4930748).sum := by decide
  have hdescent : baseEnd_4930748 < baseStart_4930748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930765 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4930765 : Nat := 118140960795 + 4930765 * 2 ^ 59
def prefixEnd_4930765 : Nat := 4983230072969 + 3 ^ 40 * 4930765 * 2
def baseEnd_4930765 : Nat := 843950813122168697653777

theorem tailTrace_4930765 : CollatzResearch.WordTrace tailWord_4930765 prefixEnd_4930765 843950813122168697653777 := by
  unfold tailWord_4930765
  simp only [CollatzResearch.WordTrace]
  refine ⟨179839773981687987463497749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119893182654458658308998499 179839773981687987463497749)
  ·
    refine ⟨8429989405391624412351457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179839773981687987463497749 8429989405391624412351457)
    ·
      refine ⟨6322492054043718309263593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8429989405391624412351457 6322492054043718309263593)
      ·
        refine ⟨4741869040532788731947695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6322492054043718309263593 4741869040532788731947695)
        ·
          refine ⟨7112803560799183097921543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741869040532788731947695 7112803560799183097921543)
          ·
            refine ⟨10669205341198774646882315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7112803560799183097921543 10669205341198774646882315)
            ·
              refine ⟨16003808011798161970323473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10669205341198774646882315 16003808011798161970323473)
              ·
                refine ⟨12002856008848621477742605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16003808011798161970323473 12002856008848621477742605)
                ·
                  refine ⟨4501071003318233054153477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12002856008848621477742605 4501071003318233054153477)
                  ·
                    refine ⟨843950813122168697653777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501071003318233054153477 843950813122168697653777)
                    ·
                      rfl

theorem cell23_4930765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4930765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930765 prefixEnd_4930765 := by exact prefixLift 4930765
  have htrace : WordTrace (prefixWord ++ tailWord_4930765) baseStart_4930765 baseEnd_4930765 := by
    simpa [prefixWord, tailWord_4930765, baseEnd_4930765] using wordTrace_append hprefix tailTrace_4930765
  have hstable : (prefixWord ++ tailWord_4930765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930765).length < 2 ^ (prefixWord ++ tailWord_4930765).sum := by decide
  have hdescent : baseEnd_4930765 < baseStart_4930765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930788 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_4930788 : Nat := 118140960795 + 4930788 * 2 ^ 59
def prefixEnd_4930788 : Nat := 4983230072969 + 3 ^ 40 * 4930788 * 2
def baseEnd_4930788 : Nat := 2531864249421559502973725

theorem tailTrace_4930788 : CollatzResearch.WordTrace tailWord_4930788 prefixEnd_4930788 2531864249421559502973725 := by
  unfold tailWord_4930788
  simp only [CollatzResearch.WordTrace]
  refine ⟨89920306430302331195792509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119893741907069774927723345 89920306430302331195792509)
  ·
    refine ⟨33720114911363374198422191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89920306430302331195792509 33720114911363374198422191)
    ·
      refine ⟨50580172367045061297633287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33720114911363374198422191 50580172367045061297633287)
      ·
        refine ⟨75870258550567591946449931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50580172367045061297633287 75870258550567591946449931)
        ·
          refine ⟨113805387825851387919674897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75870258550567591946449931 113805387825851387919674897)
          ·
            refine ⟨85354040869388540939756173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113805387825851387919674897 85354040869388540939756173)
            ·
              refine ⟨32007765326020702852408565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85354040869388540939756173 32007765326020702852408565)
              ·
                refine ⟨3000727999314440892413303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32007765326020702852408565 3000727999314440892413303)
                ·
                  refine ⟨4501091998971661338619955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000727999314440892413303 4501091998971661338619955)
                  ·
                    refine ⟨6751637998457492007929933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4501091998971661338619955 6751637998457492007929933)
                    ·
                      refine ⟨2531864249421559502973725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751637998457492007929933 2531864249421559502973725)
                      ·
                        rfl

theorem cell23_4930788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_4930788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930788 prefixEnd_4930788 := by exact prefixLift 4930788
  have htrace : WordTrace (prefixWord ++ tailWord_4930788) baseStart_4930788 baseEnd_4930788 := by
    simpa [prefixWord, tailWord_4930788, baseEnd_4930788] using wordTrace_append hprefix tailTrace_4930788
  have hstable : (prefixWord ++ tailWord_4930788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930788).length < 2 ^ (prefixWord ++ tailWord_4930788).sum := by decide
  have hdescent : baseEnd_4930788 < baseStart_4930788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930807 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_4930807 : Nat := 118140960795 + 4930807 * 2 ^ 59
def prefixEnd_4930807 : Nat := 4983230072969 + 3 ^ 40 * 4930807 * 2
def baseEnd_4930807 : Nat := 2531874005553994928636137

theorem tailTrace_4930807 : CollatzResearch.WordTrace tailWord_4930807 prefixEnd_4930807 2531874005553994928636137 := by
  unfold tailWord_4930807
  simp only [CollatzResearch.WordTrace]
  refine ⟨179841305847535828636526675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119894203898357219091017783 179841305847535828636526675)
  ·
    refine ⟨269761958771303742954790013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179841305847535828636526675 269761958771303742954790013)
    ·
      refine ⟨101160734539238903608046255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269761958771303742954790013 101160734539238903608046255)
      ·
        refine ⟨151741101808858355412069383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101160734539238903608046255 151741101808858355412069383)
        ·
          refine ⟨227611652713287533118104075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151741101808858355412069383 227611652713287533118104075)
          ·
            refine ⟨341417479069931299677156113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227611652713287533118104075 341417479069931299677156113)
            ·
              refine ⟨256063109302448474757867085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341417479069931299677156113 256063109302448474757867085)
              ·
                refine ⟨96023665988418178034200157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256063109302448474757867085 96023665988418178034200157)
                ·
                  refine ⟨36008874745656816762825059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96023665988418178034200157 36008874745656816762825059)
                  ·
                    refine ⟨54013312118485225144237589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36008874745656816762825059 54013312118485225144237589)
                    ·
                      refine ⟨2531874005553994928636137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54013312118485225144237589 2531874005553994928636137)
                      ·
                        rfl

theorem cell23_4930807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_4930807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930807 prefixEnd_4930807 := by exact prefixLift 4930807
  have htrace : WordTrace (prefixWord ++ tailWord_4930807) baseStart_4930807 baseEnd_4930807 := by
    simpa [prefixWord, tailWord_4930807, baseEnd_4930807] using wordTrace_append hprefix tailTrace_4930807
  have hstable : (prefixWord ++ tailWord_4930807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930807).length < 2 ^ (prefixWord ++ tailWord_4930807).sum := by decide
  have hdescent : baseEnd_4930807 < baseStart_4930807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930828 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_4930828 : Nat := 118140960795 + 4930828 * 2 ^ 59
def prefixEnd_4930828 : Nat := 4983230072969 + 3 ^ 40 * 4930828 * 2
def baseEnd_4930828 : Nat := 2531884788647739346473541

theorem tailTrace_4930828 : CollatzResearch.WordTrace tailWord_4930828 prefixEnd_4930828 2531884788647739346473541 := by
  unfold tailWord_4930828
  simp only [CollatzResearch.WordTrace]
  refine ⟨89921035890229874611520569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119894714520306499482027425 89921035890229874611520569)
  ·
    refine ⟨67440776917672405958640427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89921035890229874611520569 67440776917672405958640427)
    ·
      refine ⟨101161165376508608937960641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67440776917672405958640427 101161165376508608937960641)
      ·
        refine ⟨75870874032381456703470481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101161165376508608937960641 75870874032381456703470481)
        ·
          refine ⟨56903155524286092527602861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75870874032381456703470481 56903155524286092527602861)
          ·
            refine ⟨21338683321607284697851073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56903155524286092527602861 21338683321607284697851073)
            ·
              refine ⟨16004012491205463523388305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21338683321607284697851073 16004012491205463523388305)
              ·
                refine ⟨12003009368404097642541229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16004012491205463523388305 12003009368404097642541229)
                ·
                  refine ⟨4501128513151536615952961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12003009368404097642541229 4501128513151536615952961)
                  ·
                    refine ⟨3375846384863652461964721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4501128513151536615952961 3375846384863652461964721)
                    ·
                      refine ⟨2531884788647739346473541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375846384863652461964721 2531884788647739346473541)
                      ·
                        rfl

theorem cell23_4930828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_4930828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930828 prefixEnd_4930828 := by exact prefixLift 4930828
  have htrace : WordTrace (prefixWord ++ tailWord_4930828) baseStart_4930828 baseEnd_4930828 := by
    simpa [prefixWord, tailWord_4930828, baseEnd_4930828] using wordTrace_append hprefix tailTrace_4930828
  have hstable : (prefixWord ++ tailWord_4930828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930828).length < 2 ^ (prefixWord ++ tailWord_4930828).sum := by decide
  have hdescent : baseEnd_4930828 < baseStart_4930828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930904 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_4930904 : Nat := 118140960795 + 4930904 * 2 ^ 59
def prefixEnd_4930904 : Nat := 4983230072969 + 3 ^ 40 * 4930904 * 2
def baseEnd_4930904 : Nat := 2531923813177481049123191

theorem tailTrace_4930904 : CollatzResearch.WordTrace tailWord_4930904 prefixEnd_4930904 2531923813177481049123191 := by
  unfold tailWord_4930904
  simp only [CollatzResearch.WordTrace]
  refine ⟨89922421864092207101403883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119896562485456276135205177 89922421864092207101403883)
  ·
    refine ⟨134883632796138310652105825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89922421864092207101403883 134883632796138310652105825)
    ·
      refine ⟨101162724597103732989079369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134883632796138310652105825 101162724597103732989079369)
      ·
        refine ⟨75872043447827799741809527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101162724597103732989079369 75872043447827799741809527)
        ·
          refine ⟨113808065171741699612714291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75872043447827799741809527 113808065171741699612714291)
          ·
            refine ⟨170712097757612549419071437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113808065171741699612714291 170712097757612549419071437)
            ·
              refine ⟨64017036659104706032151789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170712097757612549419071437 64017036659104706032151789)
              ·
                refine ⟨24006388747164264762056921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64017036659104706032151789 24006388747164264762056921)
                ·
                  refine ⟨18004791560373198571542691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24006388747164264762056921 18004791560373198571542691)
                  ·
                    refine ⟨27007187340559797857314037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18004791560373198571542691 27007187340559797857314037)
                    ·
                      refine ⟨2531923813177481049123191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27007187340559797857314037 2531923813177481049123191)
                      ·
                        rfl

theorem cell23_4930904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_4930904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930904 prefixEnd_4930904 := by exact prefixLift 4930904
  have htrace : WordTrace (prefixWord ++ tailWord_4930904) baseStart_4930904 baseEnd_4930904 := by
    simpa [prefixWord, tailWord_4930904, baseEnd_4930904] using wordTrace_append hprefix tailTrace_4930904
  have hstable : (prefixWord ++ tailWord_4930904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930904).length < 2 ^ (prefixWord ++ tailWord_4930904).sum := by decide
  have hdescent : baseEnd_4930904 < baseStart_4930904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4930961 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 5, 2]
def baseStart_4930961 : Nat := 118140960795 + 4930961 * 2 ^ 59
def prefixEnd_4930961 : Nat := 4983230072969 + 3 ^ 40 * 4930961 * 2
def baseEnd_4930961 : Nat := 2531953081574787326110429

theorem tailTrace_4930961 : CollatzResearch.WordTrace tailWord_4930961 prefixEnd_4930961 2531953081574787326110429 := by
  unfold tailWord_4930961
  simp only [CollatzResearch.WordTrace]
  refine ⟨179846922688977912937632737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119897948459318608625088491 179846922688977912937632737)
  ·
    refine ⟨134885192016733434703224553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179846922688977912937632737 134885192016733434703224553)
    ·
      refine ⟨101163894012550076027418415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134885192016733434703224553 101163894012550076027418415)
      ·
        refine ⟨151745841018825114041127623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101163894012550076027418415 151745841018825114041127623)
        ·
          refine ⟨227618761528237671061691435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151745841018825114041127623 227618761528237671061691435)
          ·
            refine ⟨341428142292356506592537153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227618761528237671061691435 341428142292356506592537153)
            ·
              refine ⟨256071106719267379944402865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341428142292356506592537153 256071106719267379944402865)
              ·
                refine ⟨192053330039450534958302149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256071106719267379944402865 192053330039450534958302149)
                ·
                  refine ⟨36009999382396975304681653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192053330039450534958302149 36009999382396975304681653)
                  ·
                    refine ⟨3375937442099716434813905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36009999382396975304681653 3375937442099716434813905)
                    ·
                      refine ⟨2531953081574787326110429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3375937442099716434813905 2531953081574787326110429)
                      ·
                        rfl

theorem cell23_4930961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_4930961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4930961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4930961 prefixEnd_4930961 := by exact prefixLift 4930961
  have htrace : WordTrace (prefixWord ++ tailWord_4930961) baseStart_4930961 baseEnd_4930961 := by
    simpa [prefixWord, tailWord_4930961, baseEnd_4930961] using wordTrace_append hprefix tailTrace_4930961
  have hstable : (prefixWord ++ tailWord_4930961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4930961).length < 2 ^ (prefixWord ++ tailWord_4930961).sum := by decide
  have hdescent : baseEnd_4930961 < baseStart_4930961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4930961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931011 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3]
def baseStart_4931011 : Nat := 118140960795 + 4931011 * 2 ^ 59
def prefixEnd_4931011 : Nat := 4983230072969 + 3 ^ 40 * 4931011 * 2
def baseEnd_4931011 : Nat := 2531978755607512130485199

theorem tailTrace_4931011 : CollatzResearch.WordTrace tailWord_4931011 prefixEnd_4931011 2531978755607512130485199 := by
  unfold tailWord_4931011
  simp only [CollatzResearch.WordTrace]
  refine ⟨179848746338796771476952887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119899164225864514317968591 179848746338796771476952887)
  ·
    refine ⟨269773119508195157215429331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179848746338796771476952887 269773119508195157215429331)
    ·
      refine ⟨404659679262292735823143997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269773119508195157215429331 404659679262292735823143997)
      ·
        refine ⟨151747379723359775933678999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404659679262292735823143997 151747379723359775933678999)
        ·
          refine ⟨227621069585039663900518499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151747379723359775933678999 227621069585039663900518499)
          ·
            refine ⟨341431604377559495850777749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227621069585039663900518499 341431604377559495850777749)
            ·
              refine ⟨16004606455198101368005207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 341431604377559495850777749 16004606455198101368005207)
              ·
                refine ⟨24006909682797152052007811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16004606455198101368005207 24006909682797152052007811)
                ·
                  refine ⟨36010364524195728078011717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24006909682797152052007811 36010364524195728078011717)
                  ·
                    refine ⟨6751943348286699014627197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36010364524195728078011717 6751943348286699014627197)
                    ·
                      refine ⟨2531978755607512130485199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6751943348286699014627197 2531978755607512130485199)
                      ·
                        rfl

theorem cell23_4931011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_4931011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931011 prefixEnd_4931011 := by exact prefixLift 4931011
  have htrace : WordTrace (prefixWord ++ tailWord_4931011) baseStart_4931011 baseEnd_4931011 := by
    simpa [prefixWord, tailWord_4931011, baseEnd_4931011] using wordTrace_append hprefix tailTrace_4931011
  have hstable : (prefixWord ++ tailWord_4931011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931011).length < 2 ^ (prefixWord ++ tailWord_4931011).sum := by decide
  have hdescent : baseEnd_4931011 < baseStart_4931011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931068 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_4931068 : Nat := 118140960795 + 4931068 * 2 ^ 59
def prefixEnd_4931068 : Nat := 4983230072969 + 3 ^ 40 * 4931068 * 2
def baseEnd_4931068 : Nat := 2532008024004818407472437

theorem tailTrace_4931068 : CollatzResearch.WordTrace tailWord_4931068 prefixEnd_4931068 2532008024004818407472437 := by
  unfold tailWord_4931068
  simp only [CollatzResearch.WordTrace]
  refine ⟨89925412649795135105888929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119900550199726846807851905 89925412649795135105888929)
  ·
    refine ⟨67444059487346351329416697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89925412649795135105888929 67444059487346351329416697)
    ·
      refine ⟨50583044615509763497062523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67444059487346351329416697 50583044615509763497062523)
      ·
        refine ⟨75874566923264645245593785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50583044615509763497062523 75874566923264645245593785)
        ·
          refine ⟨56905925192448483934195339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75874566923264645245593785 56905925192448483934195339)
          ·
            refine ⟨85358887788672725901293009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56905925192448483934195339 85358887788672725901293009)
            ·
              refine ⟨64019165841504544425969757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85358887788672725901293009 64019165841504544425969757)
              ·
                refine ⟨24007187190564204159738659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64019165841504544425969757 24007187190564204159738659)
                ·
                  refine ⟨36010780785846306239607989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24007187190564204159738659 36010780785846306239607989)
                  ·
                    refine ⟨3376010698673091209963249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36010780785846306239607989 3376010698673091209963249)
                    ·
                      refine ⟨2532008024004818407472437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376010698673091209963249 2532008024004818407472437)
                      ·
                        rfl

theorem cell23_4931068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_4931068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931068 prefixEnd_4931068 := by exact prefixLift 4931068
  have htrace : WordTrace (prefixWord ++ tailWord_4931068) baseStart_4931068 baseEnd_4931068 := by
    simpa [prefixWord, tailWord_4931068, baseEnd_4931068] using wordTrace_append hprefix tailTrace_4931068
  have hstable : (prefixWord ++ tailWord_4931068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931068).length < 2 ^ (prefixWord ++ tailWord_4931068).sum := by decide
  have hdescent : baseEnd_4931068 < baseStart_4931068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931086 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_4931086 : Nat := 118140960795 + 4931086 * 2 ^ 59
def prefixEnd_4931086 : Nat := 4983230072969 + 3 ^ 40 * 4931086 * 2
def baseEnd_4931086 : Nat := 844005755552199779015785

theorem tailTrace_4931086 : CollatzResearch.WordTrace tailWord_4931086 prefixEnd_4931086 844005755552199779015785 := by
  unfold tailWord_4931086
  simp only [CollatzResearch.WordTrace]
  refine ⟨22481435226690632410741639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119900987875683372857288741 22481435226690632410741639)
  ·
    refine ⟨33722152840035948616112459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22481435226690632410741639 33722152840035948616112459)
    ·
      refine ⟨50583229260053922924168689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33722152840035948616112459 50583229260053922924168689)
      ·
        refine ⟨37937421945040442193126517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50583229260053922924168689 37937421945040442193126517)
        ·
          refine ⟨3556633307347541455605611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37937421945040442193126517 3556633307347541455605611)
          ·
            refine ⟨5334949961021312183408417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556633307347541455605611 5334949961021312183408417)
            ·
              refine ⟨4001212470765984137556313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5334949961021312183408417 4001212470765984137556313)
              ·
                refine ⟨3000909353074488103167235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4001212470765984137556313 3000909353074488103167235)
                ·
                  refine ⟨4501364029611732154750853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000909353074488103167235 4501364029611732154750853)
                  ·
                    refine ⟨844005755552199779015785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501364029611732154750853 844005755552199779015785)
                    ·
                      rfl

theorem cell23_4931086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_4931086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931086 prefixEnd_4931086 := by exact prefixLift 4931086
  have htrace : WordTrace (prefixWord ++ tailWord_4931086) baseStart_4931086 baseEnd_4931086 := by
    simpa [prefixWord, tailWord_4931086, baseEnd_4931086] using wordTrace_append hprefix tailTrace_4931086
  have hstable : (prefixWord ++ tailWord_4931086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931086).length < 2 ^ (prefixWord ++ tailWord_4931086).sum := by decide
  have hdescent : baseEnd_4931086 < baseStart_4931086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931098 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_4931098 : Nat := 118140960795 + 4931098 * 2 ^ 59
def prefixEnd_4931098 : Nat := 4983230072969 + 3 ^ 40 * 4931098 * 2
def baseEnd_4931098 : Nat := 2532023428424453290097299

theorem tailTrace_4931098 : CollatzResearch.WordTrace tailWord_4931098 prefixEnd_4931098 2532023428424453290097299 := by
  unfold tailWord_4931098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44962979872370396333842487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119901279659654390223579965 44962979872370396333842487)
  ·
    refine ⟨67444469808555594500763731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44962979872370396333842487 67444469808555594500763731)
    ·
      refine ⟨101166704712833391751145597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67444469808555594500763731 101166704712833391751145597)
      ·
        refine ⟨37937514267312521906679599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101166704712833391751145597 37937514267312521906679599)
        ·
          refine ⟨56906271400968782860019399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37937514267312521906679599 56906271400968782860019399)
          ·
            refine ⟨85359407101453174290029099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56906271400968782860019399 85359407101453174290029099)
            ·
              refine ⟨128039110652179761435043649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85359407101453174290029099 128039110652179761435043649)
              ·
                refine ⟨96029332989134821076282737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128039110652179761435043649 96029332989134821076282737)
                ·
                  refine ⟨72021999741851115807212053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96029332989134821076282737 72021999741851115807212053)
                  ·
                    refine ⟨3376031237899271053463065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72021999741851115807212053 3376031237899271053463065)
                    ·
                      refine ⟨2532023428424453290097299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376031237899271053463065 2532023428424453290097299)
                      ·
                        rfl

theorem cell23_4931098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_4931098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931098 prefixEnd_4931098 := by exact prefixLift 4931098
  have htrace : WordTrace (prefixWord ++ tailWord_4931098) baseStart_4931098 baseEnd_4931098 := by
    simpa [prefixWord, tailWord_4931098, baseEnd_4931098] using wordTrace_append hprefix tailTrace_4931098
  have hstable : (prefixWord ++ tailWord_4931098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931098).length < 2 ^ (prefixWord ++ tailWord_4931098).sum := by decide
  have hdescent : baseEnd_4931098 < baseStart_4931098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931126 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_4931126 : Nat := 118140960795 + 4931126 * 2 ^ 59
def prefixEnd_4931126 : Nat := 4983230072969 + 3 ^ 40 * 4931126 * 2
def baseEnd_4931126 : Nat := 2532037805882779180547171

theorem tailTrace_4931126 : CollatzResearch.WordTrace tailWord_4931126 prefixEnd_4931126 2532037805882779180547171 := by
  unfold tailWord_4931126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240808795836259132336827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119901960488920097411592821 11240808795836259132336827)
  ·
    refine ⟨16861213193754388698505241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11240808795836259132336827 16861213193754388698505241)
    ·
      refine ⟨12645909895315791523878931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16861213193754388698505241 12645909895315791523878931)
      ·
        refine ⟨18968864842973687285818397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645909895315791523878931 18968864842973687285818397)
        ·
          refine ⟨7113324316115132732181899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18968864842973687285818397 7113324316115132732181899)
          ·
            refine ⟨10669986474172699098272849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7113324316115132732181899 10669986474172699098272849)
            ·
              refine ⟨8002489855629524323704637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10669986474172699098272849 8002489855629524323704637)
              ·
                refine ⟨3000933695861071621389239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8002489855629524323704637 3000933695861071621389239)
                ·
                  refine ⟨4501400543791607432083859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000933695861071621389239 4501400543791607432083859)
                  ·
                    refine ⟨6752100815687411148125789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4501400543791607432083859 6752100815687411148125789)
                    ·
                      refine ⟨2532037805882779180547171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6752100815687411148125789 2532037805882779180547171)
                      ·
                        rfl

theorem cell23_4931126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_4931126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931126 prefixEnd_4931126 := by exact prefixLift 4931126
  have htrace : WordTrace (prefixWord ++ tailWord_4931126) baseStart_4931126 baseEnd_4931126 := by
    simpa [prefixWord, tailWord_4931126, baseEnd_4931126] using wordTrace_append hprefix tailTrace_4931126
  have hstable : (prefixWord ++ tailWord_4931126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931126).length < 2 ^ (prefixWord ++ tailWord_4931126).sum := by decide
  have hdescent : baseEnd_4931126 < baseStart_4931126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931128 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_4931128 : Nat := 118140960795 + 4931128 * 2 ^ 59
def prefixEnd_4931128 : Nat := 4983230072969 + 3 ^ 40 * 4931128 * 2
def baseEnd_4931128 : Nat := 2532038832844088172722161

theorem tailTrace_4931128 : CollatzResearch.WordTrace tailWord_4931128 prefixEnd_4931128 2532038832844088172722161 := by
  unfold tailWord_4931128
  simp only [CollatzResearch.WordTrace]
  refine ⟨89926506839686450229481019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119902009119581933639308025 89926506839686450229481019)
  ·
    refine ⟨134889760259529675344221529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89926506839686450229481019 134889760259529675344221529)
    ·
      refine ⟨101167320194647256508166147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134889760259529675344221529 101167320194647256508166147)
      ·
        refine ⟨151750980291970884762249221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101167320194647256508166147 151750980291970884762249221)
        ·
          refine ⟨28453308804744540892921729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151750980291970884762249221 28453308804744540892921729)
          ·
            refine ⟨21339981603558405669691297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28453308804744540892921729 21339981603558405669691297)
            ·
              refine ⟨16004986202668804252268473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21339981603558405669691297 16004986202668804252268473)
              ·
                refine ⟨12003739652001603189201355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16004986202668804252268473 12003739652001603189201355)
                ·
                  refine ⟨18005609478002404783802033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12003739652001603189201355 18005609478002404783802033)
                  ·
                    refine ⟨13504207108501803587851525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18005609478002404783802033 13504207108501803587851525)
                    ·
                      refine ⟨2532038832844088172722161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13504207108501803587851525 2532038832844088172722161)
                      ·
                        rfl

theorem cell23_4931128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_4931128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931128 prefixEnd_4931128 := by exact prefixLift 4931128
  have htrace : WordTrace (prefixWord ++ tailWord_4931128) baseStart_4931128 baseEnd_4931128 := by
    simpa [prefixWord, tailWord_4931128, baseEnd_4931128] using wordTrace_append hprefix tailTrace_4931128
  have hstable : (prefixWord ++ tailWord_4931128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931128).length < 2 ^ (prefixWord ++ tailWord_4931128).sum := by decide
  have hdescent : baseEnd_4931128 < baseStart_4931128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931135 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_4931135 : Nat := 118140960795 + 4931135 * 2 ^ 59
def prefixEnd_4931135 : Nat := 4983230072969 + 3 ^ 40 * 4931135 * 2
def baseEnd_4931135 : Nat := 2532042427208669645334629

theorem tailTrace_4931135 : CollatzResearch.WordTrace tailWord_4931135 prefixEnd_4931135 2532042427208669645334629 := by
  unfold tailWord_4931135
  simp only [CollatzResearch.WordTrace]
  refine ⟨179853268990347540654466859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119902179326898360436311239 179853268990347540654466859)
  ·
    refine ⟨269779903485521310981700289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179853268990347540654466859 269779903485521310981700289)
    ·
      refine ⟨202334927614140983236275217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269779903485521310981700289 202334927614140983236275217)
      ·
        refine ⟨151751195710605737427206413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202334927614140983236275217 151751195710605737427206413)
        ·
          refine ⟨56906698391477151535202405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151751195710605737427206413 56906698391477151535202405)
          ·
            refine ⟨10670005948401965912850451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56906698391477151535202405 10670005948401965912850451)
            ·
              refine ⟨16005008922602948869275677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10670005948401965912850451 16005008922602948869275677)
              ·
                refine ⟨6001878345976105825978379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16005008922602948869275677 6001878345976105825978379)
                ·
                  refine ⟨9002817518964158738967569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6001878345976105825978379 9002817518964158738967569)
                  ·
                    refine ⟨6752113139223119054225677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9002817518964158738967569 6752113139223119054225677)
                    ·
                      refine ⟨2532042427208669645334629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6752113139223119054225677 2532042427208669645334629)
                      ·
                        rfl

theorem cell23_4931135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_4931135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931135 prefixEnd_4931135 := by exact prefixLift 4931135
  have htrace : WordTrace (prefixWord ++ tailWord_4931135) baseStart_4931135 baseEnd_4931135 := by
    simpa [prefixWord, tailWord_4931135, baseEnd_4931135] using wordTrace_append hprefix tailTrace_4931135
  have hstable : (prefixWord ++ tailWord_4931135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931135).length < 2 ^ (prefixWord ++ tailWord_4931135).sum := by decide
  have hdescent : baseEnd_4931135 < baseStart_4931135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931161 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_4931161 : Nat := 118140960795 + 4931161 * 2 ^ 59
def prefixEnd_4931161 : Nat := 4983230072969 + 3 ^ 40 * 4931161 * 2
def baseEnd_4931161 : Nat := 2532055777705686543609509

theorem tailTrace_4931161 : CollatzResearch.WordTrace tailWord_4931161 prefixEnd_4931161 2532055777705686543609509 := by
  unfold tailWord_4931161
  simp only [CollatzResearch.WordTrace]
  refine ⟨179854217288253347094913337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119902811525502231396608891 179854217288253347094913337)
  ·
    refine ⟨134890662966190010321185003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179854217288253347094913337 134890662966190010321185003)
    ·
      refine ⟨202335994449285015481777505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134890662966190010321185003 202335994449285015481777505)
      ·
        refine ⟨151751995836963761611333129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202335994449285015481777505 151751995836963761611333129)
        ·
          refine ⟨113813996877722821208499847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151751995836963761611333129 113813996877722821208499847)
          ·
            refine ⟨170720995316584231812749771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113813996877722821208499847 170720995316584231812749771)
            ·
              refine ⟨256081492974876347719124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170720995316584231812749771 256081492974876347719124657)
              ·
                refine ⟨192061119731157260789343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256081492974876347719124657 192061119731157260789343493)
                ·
                  refine ⟨36011459949591986398001905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192061119731157260789343493 36011459949591986398001905)
                  ·
                    refine ⟨27008594962193989798501429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36011459949591986398001905 27008594962193989798501429)
                    ·
                      refine ⟨2532055777705686543609509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27008594962193989798501429 2532055777705686543609509)
                      ·
                        rfl

theorem cell23_4931161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_4931161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931161 prefixEnd_4931161 := by exact prefixLift 4931161
  have htrace : WordTrace (prefixWord ++ tailWord_4931161) baseStart_4931161 baseEnd_4931161 := by
    simpa [prefixWord, tailWord_4931161, baseEnd_4931161] using wordTrace_append hprefix tailTrace_4931161
  have hstable : (prefixWord ++ tailWord_4931161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931161).length < 2 ^ (prefixWord ++ tailWord_4931161).sum := by decide
  have hdescent : baseEnd_4931161 < baseStart_4931161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931175 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_4931175 : Nat := 118140960795 + 4931175 * 2 ^ 59
def prefixEnd_4931175 : Nat := 4983230072969 + 3 ^ 40 * 4931175 * 2
def baseEnd_4931175 : Nat := 2532062966434849488834445

theorem tailTrace_4931175 : CollatzResearch.WordTrace tailWord_4931175 prefixEnd_4931175 2532062966434849488834445 := by
  unfold tailWord_4931175
  simp only [CollatzResearch.WordTrace]
  refine ⟨179854727910202627485922979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119903151940135084990615319 179854727910202627485922979)
  ·
    refine ⟨269782091865303941228884469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179854727910202627485922979 269782091865303941228884469)
    ·
      refine ⟨25292071112372244490207919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269782091865303941228884469 25292071112372244490207919)
      ·
        refine ⟨37938106668558366735311879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25292071112372244490207919 37938106668558366735311879)
        ·
          refine ⟨56907160002837550102967819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37938106668558366735311879 56907160002837550102967819)
          ·
            refine ⟨85360740004256325154451729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56907160002837550102967819 85360740004256325154451729)
            ·
              refine ⟨64020555003192243865838797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85360740004256325154451729 64020555003192243865838797)
              ·
                refine ⟨24007708126197091449689549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64020555003192243865838797 24007708126197091449689549)
                ·
                  refine ⟨9002890547323909293633581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24007708126197091449689549 9002890547323909293633581)
                  ·
                    refine ⟨3376083955246465985112593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9002890547323909293633581 3376083955246465985112593)
                    ·
                      refine ⟨2532062966434849488834445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376083955246465985112593 2532062966434849488834445)
                      ·
                        rfl

theorem cell23_4931175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_4931175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931175 prefixEnd_4931175 := by exact prefixLift 4931175
  have htrace : WordTrace (prefixWord ++ tailWord_4931175) baseStart_4931175 baseEnd_4931175 := by
    simpa [prefixWord, tailWord_4931175, baseEnd_4931175] using wordTrace_append hprefix tailTrace_4931175
  have hstable : (prefixWord ++ tailWord_4931175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931175).length < 2 ^ (prefixWord ++ tailWord_4931175).sum := by decide
  have hdescent : baseEnd_4931175 < baseStart_4931175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931178 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4931178 : Nat := 118140960795 + 4931178 * 2 ^ 59
def prefixEnd_4931178 : Nat := 4983230072969 + 3 ^ 40 * 4931178 * 2
def baseEnd_4931178 : Nat := 2532064506876812977096931

theorem tailTrace_4931178 : CollatzResearch.WordTrace tailWord_4931178 prefixEnd_4931178 2532064506876812977096931 := by
  unfold tailWord_4931178
  simp only [CollatzResearch.WordTrace]
  refine ⟨44963709332297939749570547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119903224886127839332188125 44963709332297939749570547)
  ·
    refine ⟨67445563998446909624355821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44963709332297939749570547 67445563998446909624355821)
    ·
      refine ⟨25292086499417591109133433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67445563998446909624355821 25292086499417591109133433)
      ·
        refine ⟨18969064874563193331850075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25292086499417591109133433 18969064874563193331850075)
        ·
          refine ⟨28453597311844789997775113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18969064874563193331850075 28453597311844789997775113)
          ·
            refine ⟨21340197983883592498331335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28453597311844789997775113 21340197983883592498331335)
            ·
              refine ⟨32010296975825388747497003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21340197983883592498331335 32010296975825388747497003)
              ·
                refine ⟨48015445463738083121245505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32010296975825388747497003 48015445463738083121245505)
                ·
                  refine ⟨36011584097803562340934129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48015445463738083121245505 36011584097803562340934129)
                  ·
                    refine ⟨27008688073352671755700597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36011584097803562340934129 27008688073352671755700597)
                    ·
                      refine ⟨2532064506876812977096931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27008688073352671755700597 2532064506876812977096931)
                      ·
                        rfl

theorem cell23_4931178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4931178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931178 prefixEnd_4931178 := by exact prefixLift 4931178
  have htrace : WordTrace (prefixWord ++ tailWord_4931178) baseStart_4931178 baseEnd_4931178 := by
    simpa [prefixWord, tailWord_4931178, baseEnd_4931178] using wordTrace_append hprefix tailTrace_4931178
  have hstable : (prefixWord ++ tailWord_4931178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931178).length < 2 ^ (prefixWord ++ tailWord_4931178).sum := by decide
  have hdescent : baseEnd_4931178 < baseStart_4931178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931262 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_4931262 : Nat := 118140960795 + 4931262 * 2 ^ 59
def prefixEnd_4931262 : Nat := 4983230072969 + 3 ^ 40 * 4931262 * 2
def baseEnd_4931262 : Nat := 281345293250198960938505

theorem tailTrace_4931262 : CollatzResearch.WordTrace tailWord_4931262 prefixEnd_4931262 281345293250198960938505 := by
  unfold tailWord_4931262
  simp only [CollatzResearch.WordTrace]
  refine ⟨22482237632610930168042505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119905267373924960896226693 22482237632610930168042505)
  ·
    refine ⟨16861678224458197626031879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22482237632610930168042505 16861678224458197626031879)
    ·
      refine ⟨25292517336687296439047819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16861678224458197626031879 25292517336687296439047819)
      ·
        refine ⟨37938776005030944658571729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25292517336687296439047819 37938776005030944658571729)
        ·
          refine ⟨28454082003773208493928797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37938776005030944658571729 28454082003773208493928797)
          ·
            refine ⟨10670280751414953185223299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28454082003773208493928797 10670280751414953185223299)
            ·
              refine ⟨16005421127122429777834949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10670280751414953185223299 16005421127122429777834949)
              ·
                refine ⟨3001016461335455583344053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16005421127122429777834949 3001016461335455583344053)
                ·
                  refine ⟨281345293250198960938505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001016461335455583344053 281345293250198960938505)
                  ·
                    rfl

theorem cell23_4931262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_4931262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931262 prefixEnd_4931262 := by exact prefixLift 4931262
  have htrace : WordTrace (prefixWord ++ tailWord_4931262) baseStart_4931262 baseEnd_4931262 := by
    simpa [prefixWord, tailWord_4931262, baseEnd_4931262] using wordTrace_append hprefix tailTrace_4931262
  have hstable : (prefixWord ++ tailWord_4931262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931262).length < 2 ^ (prefixWord ++ tailWord_4931262).sum := by decide
  have hdescent : baseEnd_4931262 < baseStart_4931262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931292 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4931292 : Nat := 118140960795 + 4931292 * 2 ^ 59
def prefixEnd_4931292 : Nat := 4983230072969 + 3 ^ 40 * 4931292 * 2
def baseEnd_4931292 : Nat := 844041014557141843690469

theorem tailTrace_4931292 : CollatzResearch.WordTrace tailWord_4931292 prefixEnd_4931292 844041014557141843690469 := by
  unfold tailWord_4931292
  simp only [CollatzResearch.WordTrace]
  refine ⟨89929497625389378233966065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119905996833852504311954753 89929497625389378233966065)
  ·
    refine ⟨67447123219042033675474549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89929497625389378233966065 67447123219042033675474549)
    ·
      refine ⟨6323167801785190657075739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67447123219042033675474549 6323167801785190657075739)
      ·
        refine ⟨9484751702677785985613609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6323167801785190657075739 9484751702677785985613609)
        ·
          refine ⟨7113563777008339489210207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9484751702677785985613609 7113563777008339489210207)
          ·
            refine ⟨10670345665512509233815311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7113563777008339489210207 10670345665512509233815311)
            ·
              refine ⟨16005518498268763850722967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10670345665512509233815311 16005518498268763850722967)
              ·
                refine ⟨24008277747403145776084451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16005518498268763850722967 24008277747403145776084451)
                ·
                  refine ⟨36012416621104718664126677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24008277747403145776084451 36012416621104718664126677)
                  ·
                    refine ⟨844041014557141843690469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36012416621104718664126677 844041014557141843690469)
                    ·
                      rfl

theorem cell23_4931292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4931292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931292 prefixEnd_4931292 := by exact prefixLift 4931292
  have htrace : WordTrace (prefixWord ++ tailWord_4931292) baseStart_4931292 baseEnd_4931292 := by
    simpa [prefixWord, tailWord_4931292, baseEnd_4931292] using wordTrace_append hprefix tailTrace_4931292
  have hstable : (prefixWord ++ tailWord_4931292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931292).length < 2 ^ (prefixWord ++ tailWord_4931292).sum := by decide
  have hdescent : baseEnd_4931292 < baseStart_4931292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931295 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 6, 2]
def baseStart_4931295 : Nat := 118140960795 + 4931295 * 2 ^ 59
def prefixEnd_4931295 : Nat := 4983230072969 + 3 ^ 40 * 4931295 * 2
def baseEnd_4931295 : Nat := 2532124584113389019333893

theorem tailTrace_4931295 : CollatzResearch.WordTrace tailWord_4931295 prefixEnd_4931295 2532124584113389019333893 := by
  unfold tailWord_4931295
  simp only [CollatzResearch.WordTrace]
  refine ⟨179859104669767887980291339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119906069779845258653527559 179859104669767887980291339)
  ·
    refine ⟨269788657004651831970437009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179859104669767887980291339 269788657004651831970437009)
    ·
      refine ⟨202341492753488873977827757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269788657004651831970437009 202341492753488873977827757)
      ·
        refine ⟨75878059782558327741685409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202341492753488873977827757 75878059782558327741685409)
        ·
          refine ⟨56908544836918745806264057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75878059782558327741685409 56908544836918745806264057)
          ·
            refine ⟨42681408627689059354698043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56908544836918745806264057 42681408627689059354698043)
            ·
              refine ⟨64022112941533589032047065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42681408627689059354698043 64022112941533589032047065)
              ·
                refine ⟨48016584706150191774035299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64022112941533589032047065 48016584706150191774035299)
                ·
                  refine ⟨72024877059225287661052949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48016584706150191774035299 72024877059225287661052949)
                  ·
                    refine ⟨3376166112151185359111857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72024877059225287661052949 3376166112151185359111857)
                    ·
                      refine ⟨2532124584113389019333893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376166112151185359111857 2532124584113389019333893)
                      ·
                        rfl

theorem cell23_4931295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_4931295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931295 prefixEnd_4931295 := by exact prefixLift 4931295
  have htrace : WordTrace (prefixWord ++ tailWord_4931295) baseStart_4931295 baseEnd_4931295 := by
    simpa [prefixWord, tailWord_4931295, baseEnd_4931295] using wordTrace_append hprefix tailTrace_4931295
  have hstable : (prefixWord ++ tailWord_4931295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931295).length < 2 ^ (prefixWord ++ tailWord_4931295).sum := by decide
  have hdescent : baseEnd_4931295 < baseStart_4931295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931308 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_4931308 : Nat := 118140960795 + 4931308 * 2 ^ 59
def prefixEnd_4931308 : Nat := 4983230072969 + 3 ^ 40 * 4931308 * 2
def baseEnd_4931308 : Nat := 2532131259361897468471333

theorem tailTrace_4931308 : CollatzResearch.WordTrace tailWord_4931308 prefixEnd_4931308 2532131259361897468471333 := by
  unfold tailWord_4931308
  simp only [CollatzResearch.WordTrace]
  refine ⟨89929789409360395600257289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119906385879147194133676385 89929789409360395600257289)
  ·
    refine ⟨67447342057020296700192967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89929789409360395600257289 67447342057020296700192967)
    ·
      refine ⟨101171013085530445050289451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67447342057020296700192967 101171013085530445050289451)
      ·
        refine ⟨151756519628295667575434177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101171013085530445050289451 151756519628295667575434177)
        ·
          refine ⟨113817389721221750681575633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151756519628295667575434177 113817389721221750681575633)
          ·
            refine ⟨85363042290916313011181725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113817389721221750681575633 85363042290916313011181725)
            ·
              refine ⟨32011140859093617379193147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85363042290916313011181725 32011140859093617379193147)
              ·
                refine ⟨48016711288640426068789721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32011140859093617379193147 48016711288640426068789721)
                ·
                  refine ⟨36012533466480319551592291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48016711288640426068789721 36012533466480319551592291)
                  ·
                    refine ⟨54018800199720479327388437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36012533466480319551592291 54018800199720479327388437)
                    ·
                      refine ⟨2532131259361897468471333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54018800199720479327388437 2532131259361897468471333)
                      ·
                        rfl

theorem cell23_4931308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_4931308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931308 prefixEnd_4931308 := by exact prefixLift 4931308
  have htrace : WordTrace (prefixWord ++ tailWord_4931308) baseStart_4931308 baseEnd_4931308 := by
    simpa [prefixWord, tailWord_4931308, baseEnd_4931308] using wordTrace_append hprefix tailTrace_4931308
  have hstable : (prefixWord ++ tailWord_4931308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931308).length < 2 ^ (prefixWord ++ tailWord_4931308).sum := by decide
  have hdescent : baseEnd_4931308 < baseStart_4931308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931315 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3]
def baseStart_4931315 : Nat := 118140960795 + 4931315 * 2 ^ 59
def prefixEnd_4931315 : Nat := 4983230072969 + 3 ^ 40 * 4931315 * 2
def baseEnd_4931315 : Nat := 2532134853726478941083801

theorem tailTrace_4931315 : CollatzResearch.WordTrace tailWord_4931315 prefixEnd_4931315 2532134853726478941083801 := by
  unfold tailWord_4931315
  simp only [CollatzResearch.WordTrace]
  refine ⟨179859834129695431396019399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119906556086463620930679599 179859834129695431396019399)
  ·
    refine ⟨269789751194543147094029099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179859834129695431396019399 269789751194543147094029099)
    ·
      refine ⟨404684626791814720641043649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269789751194543147094029099 404684626791814720641043649)
      ·
        refine ⟨303513470093861040480782737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404684626791814720641043649 303513470093861040480782737)
        ·
          refine ⟨227635102570395780360587053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303513470093861040480782737 227635102570395780360587053)
          ·
            refine ⟨85363163463898417635220145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227635102570395780360587053 85363163463898417635220145)
            ·
              refine ⟨64022372597923813226415109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85363163463898417635220145 64022372597923813226415109)
              ·
                refine ⟨12004194862110714979952833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64022372597923813226415109 12004194862110714979952833)
                ·
                  refine ⟨9003146146583036234964625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12004194862110714979952833 9003146146583036234964625)
                  ·
                    refine ⟨6752359609937277176223469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9003146146583036234964625 6752359609937277176223469)
                    ·
                      refine ⟨2532134853726478941083801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6752359609937277176223469 2532134853726478941083801)
                      ·
                        rfl

theorem cell23_4931315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_4931315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931315 prefixEnd_4931315 := by exact prefixLift 4931315
  have htrace : WordTrace (prefixWord ++ tailWord_4931315) baseStart_4931315 baseEnd_4931315 := by
    simpa [prefixWord, tailWord_4931315, baseEnd_4931315] using wordTrace_append hprefix tailTrace_4931315
  have hstable : (prefixWord ++ tailWord_4931315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931315).length < 2 ^ (prefixWord ++ tailWord_4931315).sum := by decide
  have hdescent : baseEnd_4931315 < baseStart_4931315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931372 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_4931372 : Nat := 118140960795 + 4931372 * 2 ^ 59
def prefixEnd_4931372 : Nat := 4983230072969 + 3 ^ 40 * 4931372 * 2
def baseEnd_4931372 : Nat := 2532164122123785218071039

theorem tailTrace_4931372 : CollatzResearch.WordTrace tailWord_4931372 prefixEnd_4931372 2532164122123785218071039 := by
  unfold tailWord_4931372
  simp only [CollatzResearch.WordTrace]
  refine ⟨89930956545244465065422185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119907942060325953420562913 89930956545244465065422185)
  ·
    refine ⟨67448217408933348799066639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89930956545244465065422185 67448217408933348799066639)
    ·
      refine ⟨101172326113400023198599959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67448217408933348799066639 101172326113400023198599959)
      ·
        refine ⟨151758489170100034797899939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101172326113400023198599959 151758489170100034797899939)
        ·
          refine ⟨227637733755150052196849909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151758489170100034797899939 227637733755150052196849909)
          ·
            refine ⟨21341037539545317393454679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 227637733755150052196849909 21341037539545317393454679)
            ·
              refine ⟨32011556309317976090182019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21341037539545317393454679 32011556309317976090182019)
              ·
                refine ⟨48017334463976964135273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32011556309317976090182019 48017334463976964135273029)
                ·
                  refine ⟨9003250211995680775363693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48017334463976964135273029 9003250211995680775363693)
                  ·
                    refine ⟨3376218829498380290761385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9003250211995680775363693 3376218829498380290761385)
                    ·
                      refine ⟨2532164122123785218071039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376218829498380290761385 2532164122123785218071039)
                      ·
                        rfl

theorem cell23_4931372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_4931372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931372 prefixEnd_4931372 := by exact prefixLift 4931372
  have htrace : WordTrace (prefixWord ++ tailWord_4931372) baseStart_4931372 baseEnd_4931372 := by
    simpa [prefixWord, tailWord_4931372, baseEnd_4931372] using wordTrace_append hprefix tailTrace_4931372
  have hstable : (prefixWord ++ tailWord_4931372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931372).length < 2 ^ (prefixWord ++ tailWord_4931372).sum := by decide
  have hdescent : baseEnd_4931372 < baseStart_4931372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931412 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4931412 : Nat := 118140960795 + 4931412 * 2 ^ 59
def prefixEnd_4931412 : Nat := 4983230072969 + 3 ^ 40 * 4931412 * 2
def baseEnd_4931412 : Nat := 844061553783321687190285

theorem tailTrace_4931412 : CollatzResearch.WordTrace tailWord_4931412 prefixEnd_4931412 844061553783321687190285 := by
  unfold tailWord_4931412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89931686005172008481150245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119908914673562677974866993 89931686005172008481150245)
  ·
    refine ⟨16862191125969751590215671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89931686005172008481150245 16862191125969751590215671)
    ·
      refine ⟨25293286688954627385323507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16862191125969751590215671 25293286688954627385323507)
      ·
        refine ⟨37939930033431941077985261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25293286688954627385323507 37939930033431941077985261)
        ·
          refine ⟨14227473762536977904244473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37939930033431941077985261 14227473762536977904244473)
          ·
            refine ⟨10670605321902733428183355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14227473762536977904244473 10670605321902733428183355)
            ·
              refine ⟨16005907982854100142275033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10670605321902733428183355 16005907982854100142275033)
              ·
                refine ⟨12004430987140575106706275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16005907982854100142275033 12004430987140575106706275)
                ·
                  refine ⟨18006646480710862660059413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12004430987140575106706275 18006646480710862660059413)
                  ·
                    refine ⟨844061553783321687190285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18006646480710862660059413 844061553783321687190285)
                    ·
                      rfl

theorem cell23_4931412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4931412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931412 prefixEnd_4931412 := by exact prefixLift 4931412
  have htrace : WordTrace (prefixWord ++ tailWord_4931412) baseStart_4931412 baseEnd_4931412 := by
    simpa [prefixWord, tailWord_4931412, baseEnd_4931412] using wordTrace_append hprefix tailTrace_4931412
  have hstable : (prefixWord ++ tailWord_4931412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931412).length < 2 ^ (prefixWord ++ tailWord_4931412).sum := by decide
  have hdescent : baseEnd_4931412 < baseStart_4931412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931435 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3]
def baseStart_4931435 : Nat := 118140960795 + 4931435 * 2 ^ 59
def prefixEnd_4931435 : Nat := 4983230072969 + 3 ^ 40 * 4931435 * 2
def baseEnd_4931435 : Nat := 2532196471405018471583249

theorem tailTrace_4931435 : CollatzResearch.WordTrace tailWord_4931435 prefixEnd_4931435 2532196471405018471583249 := by
  unfold tailWord_4931435
  simp only [CollatzResearch.WordTrace]
  refine ⟨179864210889260691890387759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119909473926173794593591839 179864210889260691890387759)
  ·
    refine ⟨269796316333891037835581639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179864210889260691890387759 269796316333891037835581639)
    ·
      refine ⟨404694474500836556753372459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269796316333891037835581639 404694474500836556753372459)
      ·
        refine ⟨607041711751254835130058689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404694474500836556753372459 607041711751254835130058689)
        ·
          refine ⟨455281283813441126347544017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607041711751254835130058689 455281283813441126347544017)
          ·
            refine ⟨341460962860080844760658013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455281283813441126347544017 341460962860080844760658013)
            ·
              refine ⟨128047861072530316785246755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341460962860080844760658013 128047861072530316785246755)
              ·
                refine ⟨192071791608795475177870133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128047861072530316785246755 192071791608795475177870133)
                ·
                  refine ⟨18006730463324575797925325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192071791608795475177870133 18006730463324575797925325)
                  ·
                    refine ⟨6752523923746715924221997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18006730463324575797925325 6752523923746715924221997)
                    ·
                      refine ⟨2532196471405018471583249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6752523923746715924221997 2532196471405018471583249)
                      ·
                        rfl

theorem cell23_4931435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3].length) (baseStart_4931435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931435 prefixEnd_4931435 := by exact prefixLift 4931435
  have htrace : WordTrace (prefixWord ++ tailWord_4931435) baseStart_4931435 baseEnd_4931435 := by
    simpa [prefixWord, tailWord_4931435, baseEnd_4931435] using wordTrace_append hprefix tailTrace_4931435
  have hstable : (prefixWord ++ tailWord_4931435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931435).length < 2 ^ (prefixWord ++ tailWord_4931435).sum := by decide
  have hdescent : baseEnd_4931435 < baseStart_4931435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931452 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_4931452 : Nat := 118140960795 + 4931452 * 2 ^ 59
def prefixEnd_4931452 : Nat := 4983230072969 + 3 ^ 40 * 4931452 * 2
def baseEnd_4931452 : Nat := 2532205200576144905070671

theorem tailTrace_4931452 : CollatzResearch.WordTrace tailWord_4931452 prefixEnd_4931452 2532205200576144905070671 := by
  unfold tailWord_4931452
  simp only [CollatzResearch.WordTrace]
  refine ⟨89932415465099551896878305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119909887286799402529171073 89932415465099551896878305)
  ·
    refine ⟨67449311598824663922658729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89932415465099551896878305 67449311598824663922658729)
    ·
      refine ⟨50586983699118497941994047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67449311598824663922658729 50586983699118497941994047)
      ·
        refine ⟨75880475548677746912991071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50586983699118497941994047 75880475548677746912991071)
        ·
          refine ⟨113820713323016620369486607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75880475548677746912991071 113820713323016620369486607)
          ·
            refine ⟨170731069984524930554229911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113820713323016620369486607 170731069984524930554229911)
            ·
              refine ⟨256096604976787395831344867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170731069984524930554229911 256096604976787395831344867)
              ·
                refine ⟨384144907465181093747017301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256096604976787395831344867 384144907465181093747017301)
                ·
                  refine ⟨4501698134357590942347859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 384144907465181093747017301 4501698134357590942347859)
                  ·
                    refine ⟨6752547201536386413521789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4501698134357590942347859 6752547201536386413521789)
                    ·
                      refine ⟨2532205200576144905070671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6752547201536386413521789 2532205200576144905070671)
                      ·
                        rfl

theorem cell23_4931452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_4931452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931452 prefixEnd_4931452 := by exact prefixLift 4931452
  have htrace : WordTrace (prefixWord ++ tailWord_4931452) baseStart_4931452 baseEnd_4931452 := by
    simpa [prefixWord, tailWord_4931452, baseEnd_4931452] using wordTrace_append hprefix tailTrace_4931452
  have hstable : (prefixWord ++ tailWord_4931452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931452).length < 2 ^ (prefixWord ++ tailWord_4931452).sum := by decide
  have hdescent : baseEnd_4931452 < baseStart_4931452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931465 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_4931465 : Nat := 118140960795 + 4931465 * 2 ^ 59
def prefixEnd_4931465 : Nat := 4983230072969 + 3 ^ 40 * 4931465 * 2
def baseEnd_4931465 : Nat := 2532211875824653354208111

theorem tailTrace_4931465 : CollatzResearch.WordTrace tailWord_4931465 prefixEnd_4931465 2532211875824653354208111 := by
  unfold tailWord_4931465
  simp only [CollatzResearch.WordTrace]
  refine ⟨179865305079152007013979849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119910203386101338009319899 179865305079152007013979849)
  ·
    refine ⟨134898978809364005260484887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179865305079152007013979849 134898978809364005260484887)
    ·
      refine ⟨202348468214046007890727331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134898978809364005260484887 202348468214046007890727331)
      ·
        refine ⟨303522702321069011836090997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202348468214046007890727331 303522702321069011836090997)
        ·
          refine ⟨28455253342600219859633531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 303522702321069011836090997 28455253342600219859633531)
          ·
            refine ⟨42682880013900329789450297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28455253342600219859633531 42682880013900329789450297)
            ·
              refine ⟨32012160010425247342087723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42682880013900329789450297 32012160010425247342087723)
              ·
                refine ⟨48018240015637871013131585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32012160010425247342087723 48018240015637871013131585)
                ·
                  refine ⟨36013680011728403259848689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48018240015637871013131585 36013680011728403259848689)
                  ·
                    refine ⟨27010260008796302444886517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36013680011728403259848689 27010260008796302444886517)
                    ·
                      refine ⟨2532211875824653354208111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27010260008796302444886517 2532211875824653354208111)
                      ·
                        rfl

theorem cell23_4931465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_4931465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931465 prefixEnd_4931465 := by exact prefixLift 4931465
  have htrace : WordTrace (prefixWord ++ tailWord_4931465) baseStart_4931465 baseEnd_4931465 := by
    simpa [prefixWord, tailWord_4931465, baseEnd_4931465] using wordTrace_append hprefix tailTrace_4931465
  have hstable : (prefixWord ++ tailWord_4931465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931465).length < 2 ^ (prefixWord ++ tailWord_4931465).sum := by decide
  have hdescent : baseEnd_4931465 < baseStart_4931465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931470 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4931470 : Nat := 118140960795 + 4931470 * 2 ^ 59
def prefixEnd_4931470 : Nat := 4983230072969 + 3 ^ 40 * 4931470 * 2
def baseEnd_4931470 : Nat := 2532214443227925834645589

theorem tailTrace_4931470 : CollatzResearch.WordTrace tailWord_4931470 prefixEnd_4931470 2532214443227925834645589 := by
  unfold tailWord_4931470
  simp only [CollatzResearch.WordTrace]
  refine ⟨22483185930516736608488983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119910324962755928578607909 22483185930516736608488983)
  ·
    refine ⟨33724778895775104912733475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22483185930516736608488983 33724778895775104912733475)
    ·
      refine ⟨50587168343662657369100213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33724778895775104912733475 50587168343662657369100213)
      ·
        refine ⟨4742547032218374128353145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50587168343662657369100213 4742547032218374128353145)
        ·
          refine ⟨3556910274163780596264859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4742547032218374128353145 3556910274163780596264859)
          ·
            refine ⟨5335365411245670894397289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3556910274163780596264859 5335365411245670894397289)
            ·
              refine ⟨4001524058434253170797967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5335365411245670894397289 4001524058434253170797967)
              ·
                refine ⟨6002286087651379756196951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4001524058434253170797967 6002286087651379756196951)
                ·
                  refine ⟨9003429131477069634295427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6002286087651379756196951 9003429131477069634295427)
                  ·
                    refine ⟨13505143697215604451443141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9003429131477069634295427 13505143697215604451443141)
                    ·
                      refine ⟨2532214443227925834645589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13505143697215604451443141 2532214443227925834645589)
                      ·
                        rfl

theorem cell23_4931470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4931470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931470 prefixEnd_4931470 := by exact prefixLift 4931470
  have htrace : WordTrace (prefixWord ++ tailWord_4931470) baseStart_4931470 baseEnd_4931470 := by
    simpa [prefixWord, tailWord_4931470, baseEnd_4931470] using wordTrace_append hprefix tailTrace_4931470
  have hstable : (prefixWord ++ tailWord_4931470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931470).length < 2 ^ (prefixWord ++ tailWord_4931470).sum := by decide
  have hdescent : baseEnd_4931470 < baseStart_4931470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931562 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_4931562 : Nat := 118140960795 + 4931562 * 2 ^ 59
def prefixEnd_4931562 : Nat := 4983230072969 + 3 ^ 40 * 4931562 * 2
def baseEnd_4931562 : Nat := 844087227816046491565055

theorem tailTrace_4931562 : CollatzResearch.WordTrace tailWord_4931562 prefixEnd_4931562 844087227816046491565055 := by
  unfold tailWord_4931562
  simp only [CollatzResearch.WordTrace]
  refine ⟨44967210739950148145065235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119912561973200395053507293 44967210739950148145065235)
  ·
    refine ⟨67450816109925222217597853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44967210739950148145065235 67450816109925222217597853)
    ·
      refine ⟨25294056041221958331599195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67450816109925222217597853 25294056041221958331599195)
      ·
        refine ⟨37941084061832937497398793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25294056041221958331599195 37941084061832937497398793)
        ·
          refine ⟨28455813046374703123049095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37941084061832937497398793 28455813046374703123049095)
          ·
            refine ⟨42683719569562054684573643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28455813046374703123049095 42683719569562054684573643)
            ·
              refine ⟨64025579354343082026860465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42683719569562054684573643 64025579354343082026860465)
              ·
                refine ⟨48019184515757311520145349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64025579354343082026860465 48019184515757311520145349)
                ·
                  refine ⟨9003597096704495910027253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48019184515757311520145349 9003597096704495910027253)
                  ·
                    refine ⟨844087227816046491565055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9003597096704495910027253 844087227816046491565055)
                    ·
                      rfl

theorem cell23_4931562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_4931562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931562 prefixEnd_4931562 := by exact prefixLift 4931562
  have htrace : WordTrace (prefixWord ++ tailWord_4931562) baseStart_4931562 baseEnd_4931562 := by
    simpa [prefixWord, tailWord_4931562, baseEnd_4931562] using wordTrace_append hprefix tailTrace_4931562
  have hstable : (prefixWord ++ tailWord_4931562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931562).length < 2 ^ (prefixWord ++ tailWord_4931562).sum := by decide
  have hdescent : baseEnd_4931562 < baseStart_4931562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931626 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4931626 : Nat := 118140960795 + 4931626 * 2 ^ 59
def prefixEnd_4931626 : Nat := 4983230072969 + 3 ^ 40 * 4931626 * 2
def baseEnd_4931626 : Nat := 844098182070009074764957

theorem tailTrace_4931626 : CollatzResearch.WordTrace tailWord_4931626 prefixEnd_4931626 844098182070009074764957 := by
  unfold tailWord_4931626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44967794307892182877647683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119914118154379154340393821 44967794307892182877647683)
  ·
    refine ⟨67451691461838274316471525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44967794307892182877647683 67451691461838274316471525)
    ·
      refine ⟨12647192149094676434338411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67451691461838274316471525 12647192149094676434338411)
      ·
        refine ⟨18970788223642014651507617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12647192149094676434338411 18970788223642014651507617)
        ·
          refine ⟨14228091167731510988630713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18970788223642014651507617 14228091167731510988630713)
          ·
            refine ⟨10671068375798633241473035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14228091167731510988630713 10671068375798633241473035)
            ·
              refine ⟨16006602563697949862209553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10671068375798633241473035 16006602563697949862209553)
              ·
                refine ⟨12004951922773462396657165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16006602563697949862209553 12004951922773462396657165)
                ·
                  refine ⟨4501856971040048398746437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12004951922773462396657165 4501856971040048398746437)
                  ·
                    refine ⟨844098182070009074764957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501856971040048398746437 844098182070009074764957)
                    ·
                      rfl

theorem cell23_4931626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4931626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931626 prefixEnd_4931626 := by exact prefixLift 4931626
  have htrace : WordTrace (prefixWord ++ tailWord_4931626) baseStart_4931626 baseEnd_4931626 := by
    simpa [prefixWord, tailWord_4931626, baseEnd_4931626] using wordTrace_append hprefix tailTrace_4931626
  have hstable : (prefixWord ++ tailWord_4931626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931626).length < 2 ^ (prefixWord ++ tailWord_4931626).sum := by decide
  have hdescent : baseEnd_4931626 < baseStart_4931626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931676 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4931676 : Nat := 118140960795 + 4931676 * 2 ^ 59
def prefixEnd_4931676 : Nat := 4983230072969 + 3 ^ 40 * 4931676 * 2
def baseEnd_4931676 : Nat := 2532320220242752028669641

theorem tailTrace_4931676 : CollatzResearch.WordTrace tailWord_4931676 prefixEnd_4931676 2532320220242752028669641 := by
  unfold tailWord_4931676
  simp only [CollatzResearch.WordTrace]
  refine ⟨89936500440693795024955441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119915333920925060033273921 89936500440693795024955441)
  ·
    refine ⟨67452375330520346268716581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89936500440693795024955441 67452375330520346268716581)
    ·
      refine ⟨12647320374472564925384359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67452375330520346268716581 12647320374472564925384359)
      ·
        refine ⟨18970980561708847388076539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12647320374472564925384359 18970980561708847388076539)
        ·
          refine ⟨28456470842563271082114809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18970980561708847388076539 28456470842563271082114809)
          ·
            refine ⟨21342353131922453311586107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28456470842563271082114809 21342353131922453311586107)
            ·
              refine ⟨32013529697883679967379161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21342353131922453311586107 32013529697883679967379161)
              ·
                refine ⟨24010147273412759975534371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32013529697883679967379161 24010147273412759975534371)
                ·
                  refine ⟨36015220910119139963301557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24010147273412759975534371 36015220910119139963301557)
                  ·
                    refine ⟨3376426960323669371559521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36015220910119139963301557 3376426960323669371559521)
                    ·
                      refine ⟨2532320220242752028669641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376426960323669371559521 2532320220242752028669641)
                      ·
                        rfl

theorem cell23_4931676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4931676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931676 prefixEnd_4931676 := by exact prefixLift 4931676
  have htrace : WordTrace (prefixWord ++ tailWord_4931676) baseStart_4931676 baseEnd_4931676 := by
    simpa [prefixWord, tailWord_4931676, baseEnd_4931676] using wordTrace_append hprefix tailTrace_4931676
  have hstable : (prefixWord ++ tailWord_4931676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931676).length < 2 ^ (prefixWord ++ tailWord_4931676).sum := by decide
  have hdescent : baseEnd_4931676 < baseStart_4931676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931689 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 6, 2]
def baseStart_4931689 : Nat := 118140960795 + 4931689 * 2 ^ 59
def prefixEnd_4931689 : Nat := 4983230072969 + 3 ^ 40 * 4931689 * 2
def baseEnd_4931689 : Nat := 2532326895491260477807081

theorem tailTrace_4931689 : CollatzResearch.WordTrace tailWord_4931689 prefixEnd_4931689 2532326895491260477807081 := by
  unfold tailWord_4931689
  simp only [CollatzResearch.WordTrace]
  refine ⟨179873475030340493270134121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119915650020226995513422747 179873475030340493270134121)
  ·
    refine ⟨134905106272755369952600591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179873475030340493270134121 134905106272755369952600591)
    ·
      refine ⟨202357659409133054928900887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134905106272755369952600591 202357659409133054928900887)
      ·
        refine ⟨303536489113699582393351331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202357659409133054928900887 303536489113699582393351331)
        ·
          refine ⟨455304733670549373590026997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303536489113699582393351331 455304733670549373590026997)
          ·
            refine ⟨42684818781614003774065031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 455304733670549373590026997 42684818781614003774065031)
            ·
              refine ⟨64027228172421005661097547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42684818781614003774065031 64027228172421005661097547)
              ·
                refine ⟨96040842258631508491646321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64027228172421005661097547 96040842258631508491646321)
                ·
                  refine ⟨72030631693973631368734741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96040842258631508491646321 72030631693973631368734741)
                  ·
                    refine ⟨3376435860655013970409441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72030631693973631368734741 3376435860655013970409441)
                    ·
                      refine ⟨2532326895491260477807081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376435860655013970409441 2532326895491260477807081)
                      ·
                        rfl

theorem cell23_4931689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 6, 2].length) (baseStart_4931689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931689 prefixEnd_4931689 := by exact prefixLift 4931689
  have htrace : WordTrace (prefixWord ++ tailWord_4931689) baseStart_4931689 baseEnd_4931689 := by
    simpa [prefixWord, tailWord_4931689, baseEnd_4931689] using wordTrace_append hprefix tailTrace_4931689
  have hstable : (prefixWord ++ tailWord_4931689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931689).length < 2 ^ (prefixWord ++ tailWord_4931689).sum := by decide
  have hdescent : baseEnd_4931689 < baseStart_4931689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931709 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_4931709 : Nat := 118140960795 + 4931709 * 2 ^ 59
def prefixEnd_4931709 : Nat := 4983230072969 + 3 ^ 40 * 4931709 * 2
def baseEnd_4931709 : Nat := 2532337165104350399556989

theorem tailTrace_4931709 : CollatzResearch.WordTrace tailWord_4931709 prefixEnd_4931709 2532337165104350399556989 := by
  unfold tailWord_4931709
  simp only [CollatzResearch.WordTrace]
  refine ⟨179874204490268036685862181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119916136326845357790574787 179874204490268036685862181)
  ·
    refine ⟨33726413341925256878599159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179874204490268036685862181 33726413341925256878599159)
    ·
      refine ⟨50589620012887885317898739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33726413341925256878599159 50589620012887885317898739)
      ·
        refine ⟨75884430019331827976848109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50589620012887885317898739 75884430019331827976848109)
        ·
          refine ⟨28456661257249435491318041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75884430019331827976848109 28456661257249435491318041)
          ·
            refine ⟨21342495942937076618488531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28456661257249435491318041 21342495942937076618488531)
            ·
              refine ⟨32013743914405614927732797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21342495942937076618488531 32013743914405614927732797)
              ·
                refine ⟨12005153967902105597899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32013743914405614927732797 12005153967902105597899799)
                ·
                  refine ⟨18007730951853158396849699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12005153967902105597899799 18007730951853158396849699)
                  ·
                    refine ⟨27011596427779737595274549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18007730951853158396849699 27011596427779737595274549)
                    ·
                      refine ⟨2532337165104350399556989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27011596427779737595274549 2532337165104350399556989)
                      ·
                        rfl

theorem cell23_4931709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_4931709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931709 prefixEnd_4931709 := by exact prefixLift 4931709
  have htrace : WordTrace (prefixWord ++ tailWord_4931709) baseStart_4931709 baseEnd_4931709 := by
    simpa [prefixWord, tailWord_4931709, baseEnd_4931709] using wordTrace_append hprefix tailTrace_4931709
  have hstable : (prefixWord ++ tailWord_4931709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931709).length < 2 ^ (prefixWord ++ tailWord_4931709).sum := by decide
  have hdescent : baseEnd_4931709 < baseStart_4931709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931716 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_4931716 : Nat := 118140960795 + 4931716 * 2 ^ 59
def prefixEnd_4931716 : Nat := 4983230072969 + 3 ^ 40 * 4931716 * 2
def baseEnd_4931716 : Nat := 844113586489643957389819

theorem tailTrace_4931716 : CollatzResearch.WordTrace tailWord_4931716 prefixEnd_4931716 844113586489643957389819 := by
  unfold tailWord_4931716
  simp only [CollatzResearch.WordTrace]
  refine ⟨89937229900621338440683501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119916306534161784587578001 89937229900621338440683501)
  ·
    refine ⟨33726461212733001915256313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89937229900621338440683501 33726461212733001915256313)
    ·
      refine ⟨25294845909549751436442235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33726461212733001915256313 25294845909549751436442235)
      ·
        refine ⟨37942268864324627154663353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25294845909549751436442235 37942268864324627154663353)
        ·
          refine ⟨28456701648243470365997515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37942268864324627154663353 28456701648243470365997515)
          ·
            refine ⟨42685052472365205548996273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28456701648243470365997515 42685052472365205548996273)
            ·
              refine ⟨32013789354273904161747205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42685052472365205548996273 32013789354273904161747205)
              ·
                refine ⟨6002585503926357030327601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32013789354273904161747205 6002585503926357030327601)
                ·
                  refine ⟨4501939127944767772745701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6002585503926357030327601 4501939127944767772745701)
                  ·
                    refine ⟨844113586489643957389819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4501939127944767772745701 844113586489643957389819)
                    ·
                      rfl

theorem cell23_4931716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_4931716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931716 prefixEnd_4931716 := by exact prefixLift 4931716
  have htrace : WordTrace (prefixWord ++ tailWord_4931716) baseStart_4931716 baseEnd_4931716 := by
    simpa [prefixWord, tailWord_4931716, baseEnd_4931716] using wordTrace_append hprefix tailTrace_4931716
  have hstable : (prefixWord ++ tailWord_4931716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931716).length < 2 ^ (prefixWord ++ tailWord_4931716).sum := by decide
  have hdescent : baseEnd_4931716 < baseStart_4931716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931743 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4931743 : Nat := 118140960795 + 4931743 * 2 ^ 59
def prefixEnd_4931743 : Nat := 4983230072969 + 3 ^ 40 * 4931743 * 2
def baseEnd_4931743 : Nat := 2532354623446603266531833

theorem tailTrace_4931743 : CollatzResearch.WordTrace tailWord_4931743 prefixEnd_4931743 2532354623446603266531833 := by
  unfold tailWord_4931743
  simp only [CollatzResearch.WordTrace]
  refine ⟨179875444572144860492599883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119916963048096573661733255 179875444572144860492599883)
  ·
    refine ⟨269813166858217290738899825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179875444572144860492599883 269813166858217290738899825)
    ·
      refine ⟨202359875143662968054174869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269813166858217290738899825 202359875143662968054174869)
      ·
        refine ⟨9485619147359201627539447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202359875143662968054174869 9485619147359201627539447)
        ·
          refine ⟨14228428721038802441309171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9485619147359201627539447 14228428721038802441309171)
          ·
            refine ⟨21342643081558203661963757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14228428721038802441309171 21342643081558203661963757)
            ·
              refine ⟨8003491155584326373236409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21342643081558203661963757 8003491155584326373236409)
              ·
                refine ⟨6002618366688244779927307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8003491155584326373236409 6002618366688244779927307)
                ·
                  refine ⟨9003927550032367169890961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6002618366688244779927307 9003927550032367169890961)
                  ·
                    refine ⟨6752945662524275377418221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9003927550032367169890961 6752945662524275377418221)
                    ·
                      refine ⟨2532354623446603266531833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6752945662524275377418221 2532354623446603266531833)
                      ·
                        rfl

theorem cell23_4931743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4931743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931743 prefixEnd_4931743 := by exact prefixLift 4931743
  have htrace : WordTrace (prefixWord ++ tailWord_4931743) baseStart_4931743 baseEnd_4931743 := by
    simpa [prefixWord, tailWord_4931743, baseEnd_4931743] using wordTrace_append hprefix tailTrace_4931743
  have hstable : (prefixWord ++ tailWord_4931743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931743).length < 2 ^ (prefixWord ++ tailWord_4931743).sum := by decide
  have hdescent : baseEnd_4931743 < baseStart_4931743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931799 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_4931799 : Nat := 118140960795 + 4931799 * 2 ^ 59
def prefixEnd_4931799 : Nat := 4983230072969 + 3 ^ 40 * 4931799 * 2
def baseEnd_4931799 : Nat := 2532383378363255047431575

theorem tailTrace_4931799 : CollatzResearch.WordTrace tailWord_4931799 prefixEnd_4931799 2532383378363255047431575 := by
  unfold tailWord_4931799
  simp only [CollatzResearch.WordTrace]
  refine ⟨179877487059941982056638451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119918324706627988037758967 179877487059941982056638451)
  ·
    refine ⟨269816230589912973084957677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179877487059941982056638451 269816230589912973084957677)
    ·
      refine ⟨101181086471217364906859129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269816230589912973084957677 101181086471217364906859129)
      ·
        refine ⟨75885814853413023680144347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101181086471217364906859129 75885814853413023680144347)
        ·
          refine ⟨113828722280119535520216521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75885814853413023680144347 113828722280119535520216521)
          ·
            refine ⟨85371541710089651640162391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113828722280119535520216521 85371541710089651640162391)
            ·
              refine ⟨128057312565134477460243587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85371541710089651640162391 128057312565134477460243587)
              ·
                refine ⟨192085968847701716190365381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128057312565134477460243587 192085968847701716190365381)
                ·
                  refine ⟨36016119158944071785693509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192085968847701716190365381 36016119158944071785693509)
                  ·
                    refine ⟨6753022342302013459817533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36016119158944071785693509 6753022342302013459817533)
                    ·
                      refine ⟨2532383378363255047431575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6753022342302013459817533 2532383378363255047431575)
                      ·
                        rfl

theorem cell23_4931799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_4931799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931799 prefixEnd_4931799 := by exact prefixLift 4931799
  have htrace : WordTrace (prefixWord ++ tailWord_4931799) baseStart_4931799 baseEnd_4931799 := by
    simpa [prefixWord, tailWord_4931799, baseEnd_4931799] using wordTrace_append hprefix tailTrace_4931799
  have hstable : (prefixWord ++ tailWord_4931799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931799).length < 2 ^ (prefixWord ++ tailWord_4931799).sum := by decide
  have hdescent : baseEnd_4931799 < baseStart_4931799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931809 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_4931809 : Nat := 118140960795 + 4931809 * 2 ^ 59
def prefixEnd_4931809 : Nat := 4983230072969 + 3 ^ 40 * 4931809 * 2
def baseEnd_4931809 : Nat := 2532388513169800008306529

theorem tailTrace_4931809 : CollatzResearch.WordTrace tailWord_4931809 prefixEnd_4931809 2532388513169800008306529 := by
  unfold tailWord_4931809
  simp only [CollatzResearch.WordTrace]
  refine ⟨179877851789905753764502481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119918567859937169176334987 179877851789905753764502481)
  ·
    refine ⟨134908388842429315323376861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179877851789905753764502481 134908388842429315323376861)
    ·
      refine ⟨50590645815910993246266323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134908388842429315323376861 50590645815910993246266323)
      ·
        refine ⟨75885968723866489869399485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50590645815910993246266323 75885968723866489869399485)
        ·
          refine ⟨28457238271449933701024807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75885968723866489869399485 28457238271449933701024807)
          ·
            refine ⟨42685857407174900551537211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28457238271449933701024807 42685857407174900551537211)
            ·
              refine ⟨64028786110762350827305817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42685857407174900551537211 64028786110762350827305817)
              ·
                refine ⟨48021589583071763120479363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64028786110762350827305817 48021589583071763120479363)
                ·
                  refine ⟨72032384374607644680719045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48021589583071763120479363 72032384374607644680719045)
                  ·
                    refine ⟨13506072070238933377634821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72032384374607644680719045 13506072070238933377634821)
                    ·
                      refine ⟨2532388513169800008306529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13506072070238933377634821 2532388513169800008306529)
                      ·
                        rfl

theorem cell23_4931809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_4931809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931809 prefixEnd_4931809 := by exact prefixLift 4931809
  have htrace : WordTrace (prefixWord ++ tailWord_4931809) baseStart_4931809 baseEnd_4931809 := by
    simpa [prefixWord, tailWord_4931809, baseEnd_4931809] using wordTrace_append hprefix tailTrace_4931809
  have hstable : (prefixWord ++ tailWord_4931809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931809).length < 2 ^ (prefixWord ++ tailWord_4931809).sum := by decide
  have hdescent : baseEnd_4931809 < baseStart_4931809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931813 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4931813 : Nat := 118140960795 + 4931813 * 2 ^ 59
def prefixEnd_4931813 : Nat := 4983230072969 + 3 ^ 40 * 4931813 * 2
def baseEnd_4931813 : Nat := 2532390567092417992656511

theorem tailTrace_4931813 : CollatzResearch.WordTrace tailWord_4931813 prefixEnd_4931813 2532390567092417992656511 := by
  unfold tailWord_4931813
  simp only [CollatzResearch.WordTrace]
  refine ⟨179877997681891262447648093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119918665121260841631765395 179877997681891262447648093)
  ·
    refine ⟨67454249130709223417868035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179877997681891262447648093 67454249130709223417868035)
    ·
      refine ⟨101181373696063835126802053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67454249130709223417868035 101181373696063835126802053)
      ·
        refine ⟨18971507568011969086275385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101181373696063835126802053 18971507568011969086275385)
        ·
          refine ⟨14228630676008976814706539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18971507568011969086275385 14228630676008976814706539)
          ·
            refine ⟨21342946014013465222059809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14228630676008976814706539 21342946014013465222059809)
            ·
              refine ⟨16007209510510098916544857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21342946014013465222059809 16007209510510098916544857)
              ·
                refine ⟨12005407132882574187408643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16007209510510098916544857 12005407132882574187408643)
                ·
                  refine ⟨18008110699323861281112965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12005407132882574187408643 18008110699323861281112965)
                  ·
                    refine ⟨3376520756123223990208681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18008110699323861281112965 3376520756123223990208681)
                    ·
                      refine ⟨2532390567092417992656511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376520756123223990208681 2532390567092417992656511)
                      ·
                        rfl

theorem cell23_4931813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4931813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931813 prefixEnd_4931813 := by exact prefixLift 4931813
  have htrace : WordTrace (prefixWord ++ tailWord_4931813) baseStart_4931813 baseEnd_4931813 := by
    simpa [prefixWord, tailWord_4931813, baseEnd_4931813] using wordTrace_append hprefix tailTrace_4931813
  have hstable : (prefixWord ++ tailWord_4931813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931813).length < 2 ^ (prefixWord ++ tailWord_4931813).sum := by decide
  have hdescent : baseEnd_4931813 < baseStart_4931813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931826 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4931826 : Nat := 118140960795 + 4931826 * 2 ^ 59
def prefixEnd_4931826 : Nat := 4983230072969 + 3 ^ 40 * 4931826 * 2
def baseEnd_4931826 : Nat := 2532397242340926441793951

theorem tailTrace_4931826 : CollatzResearch.WordTrace tailWord_4931826 prefixEnd_4931826 2532397242340926441793951 := by
  unfold tailWord_4931826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44969617957711041416967833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119918981220562777111914221 44969617957711041416967833)
  ·
    refine ⟨33727213468283281062725875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44969617957711041416967833 33727213468283281062725875)
    ·
      refine ⟨50590820202424921594088813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33727213468283281062725875 50590820202424921594088813)
      ·
        refine ⟨18971557575909345597783305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50590820202424921594088813 18971557575909345597783305)
        ·
          refine ⟨14228668181932009198337479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18971557575909345597783305 14228668181932009198337479)
          ·
            refine ⟨21343002272898013797506219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14228668181932009198337479 21343002272898013797506219)
            ·
              refine ⟨32014503409347020696259329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21343002272898013797506219 32014503409347020696259329)
              ·
                refine ⟨24010877557010265522194497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32014503409347020696259329 24010877557010265522194497)
                ·
                  refine ⟨18008158167757699141645873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24010877557010265522194497 18008158167757699141645873)
                  ·
                    refine ⟨13506118625818274356234405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18008158167757699141645873 13506118625818274356234405)
                    ·
                      refine ⟨2532397242340926441793951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13506118625818274356234405 2532397242340926441793951)
                      ·
                        rfl

theorem cell23_4931826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4931826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931826 prefixEnd_4931826 := by exact prefixLift 4931826
  have htrace : WordTrace (prefixWord ++ tailWord_4931826) baseStart_4931826 baseEnd_4931826 := by
    simpa [prefixWord, tailWord_4931826, baseEnd_4931826] using wordTrace_append hprefix tailTrace_4931826
  have hstable : (prefixWord ++ tailWord_4931826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931826).length < 2 ^ (prefixWord ++ tailWord_4931826).sum := by decide
  have hdescent : baseEnd_4931826 < baseStart_4931826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931836 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 7]
def baseStart_4931836 : Nat := 118140960795 + 4931836 * 2 ^ 59
def prefixEnd_4931836 : Nat := 4983230072969 + 3 ^ 40 * 4931836 * 2
def baseEnd_4931836 : Nat := 281378041905274600296545

theorem tailTrace_4931836 : CollatzResearch.WordTrace tailWord_4931836 prefixEnd_4931836 281378041905274600296545 := by
  unfold tailWord_4931836
  simp only [CollatzResearch.WordTrace]
  refine ⟨89939418280403968687867681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119919224373871958250490241 89939418280403968687867681)
  ·
    refine ⟨67454563710302976515900761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89939418280403968687867681 67454563710302976515900761)
    ·
      refine ⟨50590922782727232386925571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67454563710302976515900761 50590922782727232386925571)
      ·
        refine ⟨75886384174090848580388357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50590922782727232386925571 75886384174090848580388357)
        ·
          refine ⟨14228697032642034108822817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75886384174090848580388357 14228697032642034108822817)
          ·
            refine ⟨10671522774481525581617113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14228697032642034108822817 10671522774481525581617113)
            ·
              refine ⟨8003642080861144186212835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10671522774481525581617113 8003642080861144186212835)
              ·
                refine ⟨12005463121291716279319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8003642080861144186212835 12005463121291716279319253)
                ·
                  refine ⟨281378041905274600296545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12005463121291716279319253 281378041905274600296545)
                  ·
                    rfl

theorem cell23_4931836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_4931836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931836 prefixEnd_4931836 := by exact prefixLift 4931836
  have htrace : WordTrace (prefixWord ++ tailWord_4931836) baseStart_4931836 baseEnd_4931836 := by
    simpa [prefixWord, tailWord_4931836, baseEnd_4931836] using wordTrace_append hprefix tailTrace_4931836
  have hstable : (prefixWord ++ tailWord_4931836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931836).length < 2 ^ (prefixWord ++ tailWord_4931836).sum := by decide
  have hdescent : baseEnd_4931836 < baseStart_4931836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931847 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4931847 : Nat := 118140960795 + 4931847 * 2 ^ 59
def prefixEnd_4931847 : Nat := 4983230072969 + 3 ^ 40 * 4931847 * 2
def baseEnd_4931847 : Nat := 2532408025434670859631355

theorem tailTrace_4931847 : CollatzResearch.WordTrace tailWord_4931847 prefixEnd_4931847 2532408025434670859631355 := by
  unfold tailWord_4931847
  simp only [CollatzResearch.WordTrace]
  refine ⟨179879237763768086254385795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119919491842512057502923863 179879237763768086254385795)
  ·
    refine ⟨269818856645652129381578693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179879237763768086254385795 269818856645652129381578693)
    ·
      refine ⟨50591035621059774259046005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269818856645652129381578693 50591035621059774259046005)
      ·
        refine ⟨4742909589474353836785563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50591035621059774259046005 4742909589474353836785563)
        ·
          refine ⟨7114364384211530755178345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742909589474353836785563 7114364384211530755178345)
          ·
            refine ⟨5335773288158648066383759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7114364384211530755178345 5335773288158648066383759)
            ·
              refine ⟨8003659932237972099575639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5335773288158648066383759 8003659932237972099575639)
              ·
                refine ⟨12005489898356958149363459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8003659932237972099575639 12005489898356958149363459)
                ·
                  refine ⟨18008234847535437224045189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12005489898356958149363459 18008234847535437224045189)
                  ·
                    refine ⟨3376544033912894479508473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18008234847535437224045189 3376544033912894479508473)
                    ·
                      refine ⟨2532408025434670859631355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376544033912894479508473 2532408025434670859631355)
                      ·
                        rfl

theorem cell23_4931847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4931847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931847 prefixEnd_4931847 := by exact prefixLift 4931847
  have htrace : WordTrace (prefixWord ++ tailWord_4931847) baseStart_4931847 baseEnd_4931847 := by
    simpa [prefixWord, tailWord_4931847, baseEnd_4931847] using wordTrace_append hprefix tailTrace_4931847
  have hstable : (prefixWord ++ tailWord_4931847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931847).length < 2 ^ (prefixWord ++ tailWord_4931847).sum := by decide
  have hdescent : baseEnd_4931847 < baseStart_4931847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931849 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_4931849 : Nat := 118140960795 + 4931849 * 2 ^ 59
def prefixEnd_4931849 : Nat := 4983230072969 + 3 ^ 40 * 4931849 * 2
def baseEnd_4931849 : Nat := 844136350798659950602115

theorem tailTrace_4931849 : CollatzResearch.WordTrace tailWord_4931849 prefixEnd_4931849 844136350798659950602115 := by
  unfold tailWord_4931849
  simp only [CollatzResearch.WordTrace]
  refine ⟨179879310709760840595958601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119919540473173893730639067 179879310709760840595958601)
  ·
    refine ⟨134909483032320630446968951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179879310709760840595958601 134909483032320630446968951)
    ·
      refine ⟨202364224548480945670453427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134909483032320630446968951 202364224548480945670453427)
      ·
        refine ⟨303546336822721418505680141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202364224548480945670453427 303546336822721418505680141)
        ·
          refine ⟨113829876308520531939630053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303546336822721418505680141 113829876308520531939630053)
          ·
            refine ⟨21343101807847599738680635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113829876308520531939630053 21343101807847599738680635)
            ·
              refine ⟨32014652711771399608020953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21343101807847599738680635 32014652711771399608020953)
              ·
                refine ⟨24010989533828549706015715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32014652711771399608020953 24010989533828549706015715)
                ·
                  refine ⟨36016484300742824559023573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24010989533828549706015715 36016484300742824559023573)
                  ·
                    refine ⟨844136350798659950602115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36016484300742824559023573 844136350798659950602115)
                    ·
                      rfl

theorem cell23_4931849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_4931849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931849 prefixEnd_4931849 := by exact prefixLift 4931849
  have htrace : WordTrace (prefixWord ++ tailWord_4931849) baseStart_4931849 baseEnd_4931849 := by
    simpa [prefixWord, tailWord_4931849, baseEnd_4931849] using wordTrace_append hprefix tailTrace_4931849
  have hstable : (prefixWord ++ tailWord_4931849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931849).length < 2 ^ (prefixWord ++ tailWord_4931849).sum := by decide
  have hdescent : baseEnd_4931849 < baseStart_4931849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931929 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_4931929 : Nat := 118140960795 + 4931929 * 2 ^ 59
def prefixEnd_4931929 : Nat := 4983230072969 + 3 ^ 40 * 4931929 * 2
def baseEnd_4931929 : Nat := 2532450130848339538805977

theorem tailTrace_4931929 : CollatzResearch.WordTrace tailWord_4931929 prefixEnd_4931929 2532450130848339538805977 := by
  unfold tailWord_4931929
  simp only [CollatzResearch.WordTrace]
  refine ⟨179882228549471014258870841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119921485699647342839247227 179882228549471014258870841)
  ·
    refine ⟨134911671412103260694153131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179882228549471014258870841 134911671412103260694153131)
    ·
      refine ⟨202367507118154891041229697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134911671412103260694153131 202367507118154891041229697)
      ·
        refine ⟨151775630338616168280922273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202367507118154891041229697 151775630338616168280922273)
        ·
          refine ⟨113831722753962126210691705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151775630338616168280922273 113831722753962126210691705)
          ·
            refine ⟨85373792065471594658018779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113831722753962126210691705 85373792065471594658018779)
            ·
              refine ⟨128060688098207391987028169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85373792065471594658018779 128060688098207391987028169)
              ·
                refine ⟨96045516073655543990271127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128060688098207391987028169 96045516073655543990271127)
                ·
                  refine ⟨144068274110483315985406691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96045516073655543990271127 144068274110483315985406691)
                  ·
                    refine ⟨216102411165724973978110037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144068274110483315985406691 216102411165724973978110037)
                    ·
                      refine ⟨2532450130848339538805977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 216102411165724973978110037 2532450130848339538805977)
                      ·
                        rfl

theorem cell23_4931929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_4931929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931929 prefixEnd_4931929 := by exact prefixLift 4931929
  have htrace : WordTrace (prefixWord ++ tailWord_4931929) baseStart_4931929 baseEnd_4931929 := by
    simpa [prefixWord, tailWord_4931929, baseEnd_4931929] using wordTrace_append hprefix tailTrace_4931929
  have hstable : (prefixWord ++ tailWord_4931929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931929).length < 2 ^ (prefixWord ++ tailWord_4931929).sum := by decide
  have hdescent : baseEnd_4931929 < baseStart_4931929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931943 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 6]
def baseStart_4931943 : Nat := 118140960795 + 4931943 * 2 ^ 59
def prefixEnd_4931943 : Nat := 4983230072969 + 3 ^ 40 * 4931943 * 2
def baseEnd_4931943 : Nat := 281384146619722498225657

theorem tailTrace_4931943 : CollatzResearch.WordTrace tailWord_4931943 prefixEnd_4931943 281384146619722498225657 := by
  unfold tailWord_4931943
  simp only [CollatzResearch.WordTrace]
  refine ⟨179882739171420294649880483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119921826114280196433253655 179882739171420294649880483)
  ·
    refine ⟨269824108757130441974820725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179882739171420294649880483 269824108757130441974820725)
    ·
      refine ⟨25296010195980978935139443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 269824108757130441974820725 25296010195980978935139443)
      ·
        refine ⟨37944015293971468402709165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25296010195980978935139443 37944015293971468402709165)
        ·
          refine ⟨14229005735239300651015937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37944015293971468402709165 14229005735239300651015937)
          ·
            refine ⟨10671754301429475488261953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14229005735239300651015937 10671754301429475488261953)
            ·
              refine ⟨8003815726072106616196465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10671754301429475488261953 8003815726072106616196465)
              ·
                refine ⟨6002861794554079962147349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8003815726072106616196465 6002861794554079962147349)
                ·
                  refine ⟨281384146619722498225657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6002861794554079962147349 281384146619722498225657)
                  ·
                    rfl

theorem cell23_4931943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 6].length) (baseStart_4931943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931943 prefixEnd_4931943 := by exact prefixLift 4931943
  have htrace : WordTrace (prefixWord ++ tailWord_4931943) baseStart_4931943 baseEnd_4931943 := by
    simpa [prefixWord, tailWord_4931943, baseEnd_4931943] using wordTrace_append hprefix tailTrace_4931943
  have hstable : (prefixWord ++ tailWord_4931943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931943).length < 2 ^ (prefixWord ++ tailWord_4931943).sum := by decide
  have hdescent : baseEnd_4931943 < baseStart_4931943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931953 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_4931953 : Nat := 118140960795 + 4931953 * 2 ^ 59
def prefixEnd_4931953 : Nat := 4983230072969 + 3 ^ 40 * 4931953 * 2
def baseEnd_4931953 : Nat := 2532462454384047444905867

theorem tailTrace_4931953 : CollatzResearch.WordTrace tailWord_4931953 prefixEnd_4931953 2532462454384047444905867 := by
  unfold tailWord_4931953
  simp only [CollatzResearch.WordTrace]
  refine ⟨179883103901384066357744513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119922069267589377571829675 179883103901384066357744513)
  ·
    refine ⟨134912327926038049768308385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179883103901384066357744513 134912327926038049768308385)
    ·
      refine ⟨101184245944528537326231289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134912327926038049768308385 101184245944528537326231289)
      ·
        refine ⟨75888184458396402994673467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101184245944528537326231289 75888184458396402994673467)
        ·
          refine ⟨113832276687594604492010201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75888184458396402994673467 113832276687594604492010201)
          ·
            refine ⟨85374207515695953369007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113832276687594604492010201 85374207515695953369007651)
            ·
              refine ⟨128061311273543930053511477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85374207515695953369007651 128061311273543930053511477)
              ·
                refine ⟨12005747931894743442516701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128061311273543930053511477 12005747931894743442516701)
                ·
                  refine ⟨4502155474460528790943763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12005747931894743442516701 4502155474460528790943763)
                  ·
                    refine ⟨6753233211690793186415645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502155474460528790943763 6753233211690793186415645)
                    ·
                      refine ⟨2532462454384047444905867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6753233211690793186415645 2532462454384047444905867)
                      ·
                        rfl

theorem cell23_4931953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_4931953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931953 prefixEnd_4931953 := by exact prefixLift 4931953
  have htrace : WordTrace (prefixWord ++ tailWord_4931953) baseStart_4931953 baseEnd_4931953 := by
    simpa [prefixWord, tailWord_4931953, baseEnd_4931953] using wordTrace_append hprefix tailTrace_4931953
  have hstable : (prefixWord ++ tailWord_4931953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931953).length < 2 ^ (prefixWord ++ tailWord_4931953).sum := by decide
  have hdescent : baseEnd_4931953 < baseStart_4931953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931980 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_4931980 : Nat := 118140960795 + 4931980 * 2 ^ 59
def prefixEnd_4931980 : Nat := 4983230072969 + 3 ^ 40 * 4931980 * 2
def baseEnd_4931980 : Nat := 2532476318361718839268243

theorem tailTrace_4931980 : CollatzResearch.WordTrace tailWord_4931980 prefixEnd_4931980 2532476318361718839268243 := by
  unfold tailWord_4931980
  simp only [CollatzResearch.WordTrace]
  refine ⟨89942044336143124984488697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119922725781524166645984929 89942044336143124984488697)
  ·
    refine ⟨67456533252107343738366523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89942044336143124984488697 67456533252107343738366523)
    ·
      refine ⟨101184799878161015607549785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67456533252107343738366523 101184799878161015607549785)
      ·
        refine ⟨75888599908620761705662339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101184799878161015607549785 75888599908620761705662339)
        ·
          refine ⟨113832899862931142558493509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75888599908620761705662339 113832899862931142558493509)
          ·
            refine ⟨21343668724299589229717533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113832899862931142558493509 21343668724299589229717533)
            ·
              refine ⟨8003875771612345961144075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21343668724299589229717533 8003875771612345961144075)
              ·
                refine ⟨12005813657418518941716113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8003875771612345961144075 12005813657418518941716113)
                ·
                  refine ⟨9004360243063889206287085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12005813657418518941716113 9004360243063889206287085)
                  ·
                    refine ⟨3376635091148958452357657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9004360243063889206287085 3376635091148958452357657)
                    ·
                      refine ⟨2532476318361718839268243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376635091148958452357657 2532476318361718839268243)
                      ·
                        rfl

theorem cell23_4931980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_4931980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931980 prefixEnd_4931980 := by exact prefixLift 4931980
  have htrace : WordTrace (prefixWord ++ tailWord_4931980) baseStart_4931980 baseEnd_4931980 := by
    simpa [prefixWord, tailWord_4931980, baseEnd_4931980] using wordTrace_append hprefix tailTrace_4931980
  have hstable : (prefixWord ++ tailWord_4931980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931980).length < 2 ^ (prefixWord ++ tailWord_4931980).sum := by decide
  have hdescent : baseEnd_4931980 < baseStart_4931980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4931993 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_4931993 : Nat := 118140960795 + 4931993 * 2 ^ 59
def prefixEnd_4931993 : Nat := 4983230072969 + 3 ^ 40 * 4931993 * 2
def baseEnd_4931993 : Nat := 2532482993610227288405683

theorem tailTrace_4931993 : CollatzResearch.WordTrace tailWord_4931993 prefixEnd_4931993 2532482993610227288405683 := by
  unfold tailWord_4931993
  simp only [CollatzResearch.WordTrace]
  refine ⟨179884562821239153189200633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119923041880826102126133755 179884562821239153189200633)
  ·
    refine ⟨134913422115929364891900475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179884562821239153189200633 134913422115929364891900475)
    ·
      refine ⟨202370133173894047337850713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134913422115929364891900475 202370133173894047337850713)
      ·
        refine ⟨151777599880420535503388035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202370133173894047337850713 151777599880420535503388035)
        ·
          refine ⟨227666399820630803255082053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151777599880420535503388035 227666399820630803255082053)
          ·
            refine ⟨42687449966368275610327885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227666399820630803255082053 42687449966368275610327885)
            ·
              refine ⟨16007793737388103353872957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42687449966368275610327885 16007793737388103353872957)
              ·
                refine ⟨6002922651520538757702359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16007793737388103353872957 6002922651520538757702359)
                ·
                  refine ⟨9004383977280808136553539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6002922651520538757702359 9004383977280808136553539)
                  ·
                    refine ⟨13506575965921212204830309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9004383977280808136553539 13506575965921212204830309)
                    ·
                      refine ⟨2532482993610227288405683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13506575965921212204830309 2532482993610227288405683)
                      ·
                        rfl

theorem cell23_4931993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_4931993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4931993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4931993 prefixEnd_4931993 := by exact prefixLift 4931993
  have htrace : WordTrace (prefixWord ++ tailWord_4931993) baseStart_4931993 baseEnd_4931993 := by
    simpa [prefixWord, tailWord_4931993, baseEnd_4931993] using wordTrace_append hprefix tailTrace_4931993
  have hstable : (prefixWord ++ tailWord_4931993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4931993).length < 2 ^ (prefixWord ++ tailWord_4931993).sum := by decide
  have hdescent : baseEnd_4931993 < baseStart_4931993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4931993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932003 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 4, 4]
def baseStart_4932003 : Nat := 118140960795 + 4932003 * 2 ^ 59
def prefixEnd_4932003 : Nat := 4983230072969 + 3 ^ 40 * 4932003 * 2
def baseEnd_4932003 : Nat := 844162709472257416426879

theorem tailTrace_4932003 : CollatzResearch.WordTrace tailWord_4932003 prefixEnd_4932003 844162709472257416426879 := by
  unfold tailWord_4932003
  simp only [CollatzResearch.WordTrace]
  refine ⟨179884927551202924897064663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119923285034135283264709775 179884927551202924897064663)
  ·
    refine ⟨269827391326804387345596995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179884927551202924897064663 269827391326804387345596995)
    ·
      refine ⟨404741086990206581018395493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269827391326804387345596995 404741086990206581018395493)
      ·
        refine ⟨75888953810663733940949155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 404741086990206581018395493 75888953810663733940949155)
        ·
          refine ⟨113833430715995600911423733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75888953810663733940949155 113833430715995600911423733)
          ·
            refine ⟨10671884129624587585445975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113833430715995600911423733 10671884129624587585445975)
            ·
              refine ⟨16007826194436881378168963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10671884129624587585445975 16007826194436881378168963)
              ·
                refine ⟨24011739291655322067253445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16007826194436881378168963 24011739291655322067253445)
                ·
                  refine ⟨4502201117185372887610021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24011739291655322067253445 4502201117185372887610021)
                  ·
                    refine ⟨844162709472257416426879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4502201117185372887610021 844162709472257416426879)
                    ·
                      rfl

theorem cell23_4932003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 4].length) (baseStart_4932003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932003 prefixEnd_4932003 := by exact prefixLift 4932003
  have htrace : WordTrace (prefixWord ++ tailWord_4932003) baseStart_4932003 baseEnd_4932003 := by
    simpa [prefixWord, tailWord_4932003, baseEnd_4932003] using wordTrace_append hprefix tailTrace_4932003
  have hstable : (prefixWord ++ tailWord_4932003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932003).length < 2 ^ (prefixWord ++ tailWord_4932003).sum := by decide
  have hdescent : baseEnd_4932003 < baseStart_4932003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932023 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_4932023 : Nat := 118140960795 + 4932023 * 2 ^ 59
def prefixEnd_4932023 : Nat := 4983230072969 + 3 ^ 40 * 4932023 * 2
def baseEnd_4932023 : Nat := 2532498398029862171030545

theorem tailTrace_4932023 : CollatzResearch.WordTrace tailWord_4932023 prefixEnd_4932023 2532498398029862171030545 := by
  unfold tailWord_4932023
  simp only [CollatzResearch.WordTrace]
  refine ⟨179885657011130468312792723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119923771340753645541861815 179885657011130468312792723)
  ·
    refine ⟨269828485516695702469189085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179885657011130468312792723 269828485516695702469189085)
    ·
      refine ⟨101185682068760888425945907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269828485516695702469189085 101185682068760888425945907)
      ·
        refine ⟨151778523103141332638918861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101185682068760888425945907 151778523103141332638918861)
        ·
          refine ⟨56916946163677999739594573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151778523103141332638918861 56916946163677999739594573)
          ·
            refine ⟨21343854811379249902347965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56916946163677999739594573 21343854811379249902347965)
            ·
              refine ⟨8003945554267218713380487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21343854811379249902347965 8003945554267218713380487)
              ·
                refine ⟨12005918331400828070070731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8003945554267218713380487 12005918331400828070070731)
                ·
                  refine ⟨18008877497101242105106097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12005918331400828070070731 18008877497101242105106097)
                  ·
                    refine ⟨13506658122825931578829573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18008877497101242105106097 13506658122825931578829573)
                    ·
                      refine ⟨2532498398029862171030545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13506658122825931578829573 2532498398029862171030545)
                      ·
                        rfl

theorem cell23_4932023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_4932023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932023 prefixEnd_4932023 := by exact prefixLift 4932023
  have htrace : WordTrace (prefixWord ++ tailWord_4932023) baseStart_4932023 baseEnd_4932023 := by
    simpa [prefixWord, tailWord_4932023, baseEnd_4932023] using wordTrace_append hprefix tailTrace_4932023
  have hstable : (prefixWord ++ tailWord_4932023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932023).length < 2 ^ (prefixWord ++ tailWord_4932023).sum := by decide
  have hdescent : baseEnd_4932023 < baseStart_4932023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932030 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_4932030 : Nat := 118140960795 + 4932030 * 2 ^ 59
def prefixEnd_4932030 : Nat := 4983230072969 + 3 ^ 40 * 4932030 * 2
def baseEnd_4932030 : Nat := 2532501992394443643643013

theorem tailTrace_4932030 : CollatzResearch.WordTrace tailWord_4932030 prefixEnd_4932030 2532501992394443643643013 := by
  unfold tailWord_4932030
  simp only [CollatzResearch.WordTrace]
  refine ⟨22485739040263138563537193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119923941548070072338865029 22485739040263138563537193)
  ·
    refine ⟨16864304280197353922652895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22485739040263138563537193 16864304280197353922652895)
    ·
      refine ⟨25296456420296030883979343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16864304280197353922652895 25296456420296030883979343)
      ·
        refine ⟨37944684630444046325969015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25296456420296030883979343 37944684630444046325969015)
        ·
          refine ⟨56917026945666069488953523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37944684630444046325969015 56917026945666069488953523)
          ·
            refine ⟨85375540418499104233430285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56917026945666069488953523 85375540418499104233430285)
            ·
              refine ⟨32015827656937164087536357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85375540418499104233430285 32015827656937164087536357)
              ·
                refine ⟨6002967685675718266413067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32015827656937164087536357 6002967685675718266413067)
                ·
                  refine ⟨9004451528513577399619601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6002967685675718266413067 9004451528513577399619601)
                  ·
                    refine ⟨6753338646385183049714701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9004451528513577399619601 6753338646385183049714701)
                    ·
                      refine ⟨2532501992394443643643013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6753338646385183049714701 2532501992394443643643013)
                      ·
                        rfl

theorem cell23_4932030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_4932030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932030 prefixEnd_4932030 := by exact prefixLift 4932030
  have htrace : WordTrace (prefixWord ++ tailWord_4932030) baseStart_4932030 baseEnd_4932030 := by
    simpa [prefixWord, tailWord_4932030, baseEnd_4932030] using wordTrace_append hprefix tailTrace_4932030
  have hstable : (prefixWord ++ tailWord_4932030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932030).length < 2 ^ (prefixWord ++ tailWord_4932030).sum := by decide
  have hdescent : baseEnd_4932030 < baseStart_4932030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932046 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_4932046 : Nat := 118140960795 + 4932046 * 2 ^ 59
def prefixEnd_4932046 : Nat := 4983230072969 + 3 ^ 40 * 4932046 * 2
def baseEnd_4932046 : Nat := 844170069361638527014313

theorem tailTrace_4932046 : CollatzResearch.WordTrace tailWord_4932046 prefixEnd_4932046 844170069361638527014313 := by
  unfold tailWord_4932046
  simp only [CollatzResearch.WordTrace]
  refine ⟨22485811986255892905109999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119924330593364762160586661 22485811986255892905109999)
  ·
    refine ⟨33728717979383839357664999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22485811986255892905109999 33728717979383839357664999)
    ·
      refine ⟨50593076969075759036497499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33728717979383839357664999 50593076969075759036497499)
      ·
        refine ⟨75889615453613638554746249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50593076969075759036497499 75889615453613638554746249)
        ·
          refine ⟨56917211590210228916059687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75889615453613638554746249 56917211590210228916059687)
          ·
            refine ⟨85375817385315343374089531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56917211590210228916059687 85375817385315343374089531)
            ·
              refine ⟨128063726077973015061134297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85375817385315343374089531 128063726077973015061134297)
              ·
                refine ⟨96047794558479761295850723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128063726077973015061134297 96047794558479761295850723)
                ·
                  refine ⟨144071691837719641943776085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96047794558479761295850723 144071691837719641943776085)
                  ·
                    refine ⟨844170069361638527014313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144071691837719641943776085 844170069361638527014313)
                    ·
                      rfl

theorem cell23_4932046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_4932046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932046 prefixEnd_4932046 := by exact prefixLift 4932046
  have htrace : WordTrace (prefixWord ++ tailWord_4932046) baseStart_4932046 baseEnd_4932046 := by
    simpa [prefixWord, tailWord_4932046, baseEnd_4932046] using wordTrace_append hprefix tailTrace_4932046
  have hstable : (prefixWord ++ tailWord_4932046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932046).length < 2 ^ (prefixWord ++ tailWord_4932046).sum := by decide
  have hdescent : baseEnd_4932046 < baseStart_4932046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932050 : List Nat := [3, 2, 2, 4, 1, 2, 9]
def baseStart_4932050 : Nat := 118140960795 + 4932050 * 2 ^ 59
def prefixEnd_4932050 : Nat := 4983230072969 + 3 ^ 40 * 4932050 * 2
def baseEnd_4932050 : Nat := 31265583481574488461641

theorem tailTrace_4932050 : CollatzResearch.WordTrace tailWord_4932050 prefixEnd_4932050 31265583481574488461641 := by
  unfold tailWord_4932050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44971660445508162981006401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119924427854688434616017069 44971660445508162981006401)
  ·
    refine ⟨33728745334131122235754801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44971660445508162981006401 33728745334131122235754801)
    ·
      refine ⟨25296559000598341676816101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33728745334131122235754801 25296559000598341676816101)
      ·
        refine ⟨4743104812612189064403019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25296559000598341676816101 4743104812612189064403019)
        ·
          refine ⟨7114657218918283596604529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743104812612189064403019 7114657218918283596604529)
          ·
            refine ⟨5335992914188712697453397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7114657218918283596604529 5335992914188712697453397)
            ·
              refine ⟨31265583481574488461641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5335992914188712697453397 31265583481574488461641)
              ·
                rfl

theorem cell23_4932050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 9].length) (baseStart_4932050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932050 prefixEnd_4932050 := by exact prefixLift 4932050
  have htrace : WordTrace (prefixWord ++ tailWord_4932050) baseStart_4932050 baseEnd_4932050 := by
    simpa [prefixWord, tailWord_4932050, baseEnd_4932050] using wordTrace_append hprefix tailTrace_4932050
  have hstable : (prefixWord ++ tailWord_4932050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932050).length < 2 ^ (prefixWord ++ tailWord_4932050).sum := by decide
  have hdescent : baseEnd_4932050 < baseStart_4932050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932056 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_4932056 : Nat := 118140960795 + 4932056 * 2 ^ 59
def prefixEnd_4932056 : Nat := 4983230072969 + 3 ^ 40 * 4932056 * 2
def baseEnd_4932056 : Nat := 2532515342891460541917893

theorem tailTrace_4932056 : CollatzResearch.WordTrace tailWord_4932056 prefixEnd_4932056 2532515342891460541917893 := by
  unfold tailWord_4932056
  simp only [CollatzResearch.WordTrace]
  refine ⟨89943430310005457474372011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119924573746673943299162681 89943430310005457474372011)
  ·
    refine ⟨134915145465008186211558017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89943430310005457474372011 134915145465008186211558017)
    ·
      refine ⟨101186359098756139658668513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134915145465008186211558017 101186359098756139658668513)
      ·
        refine ⟨75889769324067104744001385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101186359098756139658668513 75889769324067104744001385)
        ·
          refine ⟨56917326993050328558001039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75889769324067104744001385 56917326993050328558001039)
          ·
            refine ⟨85375990489575492837001559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56917326993050328558001039 85375990489575492837001559)
            ·
              refine ⟨128063985734363239255502339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85375990489575492837001559 128063985734363239255502339)
              ·
                refine ⟨192095978601544858883253509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128063985734363239255502339 192095978601544858883253509)
                ·
                  refine ⟨36017995987789661040610033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192095978601544858883253509 36017995987789661040610033)
                  ·
                    refine ⟨27013496990842245780457525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36017995987789661040610033 27013496990842245780457525)
                    ·
                      refine ⟨2532515342891460541917893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27013496990842245780457525 2532515342891460541917893)
                      ·
                        rfl

theorem cell23_4932056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_4932056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932056 prefixEnd_4932056 := by exact prefixLift 4932056
  have htrace : WordTrace (prefixWord ++ tailWord_4932056) baseStart_4932056 baseEnd_4932056 := by
    simpa [prefixWord, tailWord_4932056, baseEnd_4932056] using wordTrace_append hprefix tailTrace_4932056
  have hstable : (prefixWord ++ tailWord_4932056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932056).length < 2 ^ (prefixWord ++ tailWord_4932056).sum := by decide
  have hdescent : baseEnd_4932056 < baseStart_4932056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932061 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4932061 : Nat := 118140960795 + 4932061 * 2 ^ 59
def prefixEnd_4932061 : Nat := 4983230072969 + 3 ^ 40 * 4932061 * 2
def baseEnd_4932061 : Nat := 2532517910294733022355371

theorem tailTrace_4932061 : CollatzResearch.WordTrace tailWord_4932061 prefixEnd_4932061 2532517910294733022355371 := by
  unfold tailWord_4932061
  simp only [CollatzResearch.WordTrace]
  refine ⟨179887042984992800802676037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119924695323328533868450691 179887042984992800802676037)
  ·
    refine ⟨33728820559686150150501757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179887042984992800802676037 33728820559686150150501757)
    ·
      refine ⟨12648307709882306306438159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33728820559686150150501757 12648307709882306306438159)
      ·
        refine ⟨18972461564823459459657239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12648307709882306306438159 18972461564823459459657239)
        ·
          refine ⟨28458692347235189189485859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18972461564823459459657239 28458692347235189189485859)
          ·
            refine ⟨42688038520852783784228789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28458692347235189189485859 42688038520852783784228789)
            ·
              refine ⟨4002003611329948479771449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42688038520852783784228789 4002003611329948479771449)
              ·
                refine ⟨3001502708497461359828587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002003611329948479771449 3001502708497461359828587)
                ·
                  refine ⟨4502254062746192039742881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001502708497461359828587 4502254062746192039742881)
                  ·
                    refine ⟨3376690547059644029807161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4502254062746192039742881 3376690547059644029807161)
                    ·
                      refine ⟨2532517910294733022355371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376690547059644029807161 2532517910294733022355371)
                      ·
                        rfl

theorem cell23_4932061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4932061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932061 prefixEnd_4932061 := by exact prefixLift 4932061
  have htrace : WordTrace (prefixWord ++ tailWord_4932061) baseStart_4932061 baseEnd_4932061 := by
    simpa [prefixWord, tailWord_4932061, baseEnd_4932061] using wordTrace_append hprefix tailTrace_4932061
  have hstable : (prefixWord ++ tailWord_4932061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932061).length < 2 ^ (prefixWord ++ tailWord_4932061).sum := by decide
  have hdescent : baseEnd_4932061 < baseStart_4932061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932076 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_4932076 : Nat := 118140960795 + 4932076 * 2 ^ 59
def prefixEnd_4932076 : Nat := 4983230072969 + 3 ^ 40 * 4932076 * 2
def baseEnd_4932076 : Nat := 844175204168183487889267

theorem tailTrace_4932076 : CollatzResearch.WordTrace tailWord_4932076 prefixEnd_4932076 844175204168183487889267 := by
  unfold tailWord_4932076
  simp only [CollatzResearch.WordTrace]
  refine ⟨89943795039969229182236041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119925060053292305576314721 89943795039969229182236041)
  ·
    refine ⟨67457846279976921886677031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89943795039969229182236041 67457846279976921886677031)
    ·
      refine ⟨101186769419965382830015547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67457846279976921886677031 101186769419965382830015547)
      ·
        refine ⟨151780154129948074245023321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101186769419965382830015547 151780154129948074245023321)
        ·
          refine ⟨113835115597461055683767491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151780154129948074245023321 113835115597461055683767491)
          ·
            refine ⟨170752673396191583525651237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113835115597461055683767491 170752673396191583525651237)
            ·
              refine ⟨32016126261785921911059607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170752673396191583525651237 32016126261785921911059607)
              ·
                refine ⟨48024189392678882866589411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32016126261785921911059607 48024189392678882866589411)
                ·
                  refine ⟨72036284089018324299884117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48024189392678882866589411 72036284089018324299884117)
                  ·
                    refine ⟨844175204168183487889267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72036284089018324299884117 844175204168183487889267)
                    ·
                      rfl

theorem cell23_4932076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_4932076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932076 prefixEnd_4932076 := by exact prefixLift 4932076
  have htrace : WordTrace (prefixWord ++ tailWord_4932076) baseStart_4932076 baseEnd_4932076 := by
    simpa [prefixWord, tailWord_4932076, baseEnd_4932076] using wordTrace_append hprefix tailTrace_4932076
  have hstable : (prefixWord ++ tailWord_4932076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932076).length < 2 ^ (prefixWord ++ tailWord_4932076).sum := by decide
  have hdescent : baseEnd_4932076 < baseStart_4932076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932133 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_4932133 : Nat := 118140960795 + 4932133 * 2 ^ 59
def prefixEnd_4932133 : Nat := 4983230072969 + 3 ^ 40 * 4932133 * 2
def baseEnd_4932133 : Nat := 2532554880901856740655039

theorem tailTrace_4932133 : CollatzResearch.WordTrace tailWord_4932133 prefixEnd_4932133 2532554880901856740655039 := by
  unfold tailWord_4932133
  simp only [CollatzResearch.WordTrace]
  refine ⟨179889669040731957099297053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119926446027154638066198035 179889669040731957099297053)
  ·
    refine ⟨67458625890274483912236395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179889669040731957099297053 67458625890274483912236395)
    ·
      refine ⟨101187938835411725868354593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67458625890274483912236395 101187938835411725868354593)
      ·
        refine ⟨75890954126558794401265945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101187938835411725868354593 75890954126558794401265945)
        ·
          refine ⟨56918215594919095800949459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75890954126558794401265945 56918215594919095800949459)
          ·
            refine ⟨85377323392378643701424189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56918215594919095800949459 85377323392378643701424189)
            ·
              refine ⟨32016496272141991388034071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85377323392378643701424189 32016496272141991388034071)
              ·
                refine ⟨48024744408212987082051107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32016496272141991388034071 48024744408212987082051107)
                ·
                  refine ⟨72037116612319480623076661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48024744408212987082051107 72037116612319480623076661)
                  ·
                    refine ⟨6753479682404951308413437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72037116612319480623076661 6753479682404951308413437)
                    ·
                      refine ⟨2532554880901856740655039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6753479682404951308413437 2532554880901856740655039)
                      ·
                        rfl

theorem cell23_4932133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_4932133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932133 prefixEnd_4932133 := by exact prefixLift 4932133
  have htrace : WordTrace (prefixWord ++ tailWord_4932133) baseStart_4932133 baseEnd_4932133 := by
    simpa [prefixWord, tailWord_4932133, baseEnd_4932133] using wordTrace_append hprefix tailTrace_4932133
  have hstable : (prefixWord ++ tailWord_4932133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932133).length < 2 ^ (prefixWord ++ tailWord_4932133).sum := by decide
  have hdescent : baseEnd_4932133 < baseStart_4932133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932153 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_4932153 : Nat := 118140960795 + 4932153 * 2 ^ 59
def prefixEnd_4932153 : Nat := 4983230072969 + 3 ^ 40 * 4932153 * 2
def baseEnd_4932153 : Nat := 844188383504982220801649

theorem tailTrace_4932153 : CollatzResearch.WordTrace tailWord_4932153 prefixEnd_4932153 844188383504982220801649 := by
  unfold tailWord_4932153
  simp only [CollatzResearch.WordTrace]
  refine ⟨179890398500659500515025113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119926932333773000343350075 179890398500659500515025113)
  ·
    refine ⟨134917798875494625386268835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179890398500659500515025113 134917798875494625386268835)
    ·
      refine ⟨202376698313241938079403253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134917798875494625386268835 202376698313241938079403253)
      ·
        refine ⟨18972815466866431694944055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202376698313241938079403253 18972815466866431694944055)
        ·
          refine ⟨28459223200299647542416083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18972815466866431694944055 28459223200299647542416083)
          ·
            refine ⟨42688834800449471313624125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28459223200299647542416083 42688834800449471313624125)
            ·
              refine ⟨16008313050168551742609047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42688834800449471313624125 16008313050168551742609047)
              ·
                refine ⟨24012469575252827613913571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16008313050168551742609047 24012469575252827613913571)
                ·
                  refine ⟨36018704362879241420870357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24012469575252827613913571 36018704362879241420870357)
                  ·
                    refine ⟨844188383504982220801649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36018704362879241420870357 844188383504982220801649)
                    ·
                      rfl

theorem cell23_4932153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_4932153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932153 prefixEnd_4932153 := by exact prefixLift 4932153
  have htrace : WordTrace (prefixWord ++ tailWord_4932153) baseStart_4932153 baseEnd_4932153 := by
    simpa [prefixWord, tailWord_4932153, baseEnd_4932153] using wordTrace_append hprefix tailTrace_4932153
  have hstable : (prefixWord ++ tailWord_4932153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932153).length < 2 ^ (prefixWord ++ tailWord_4932153).sum := by decide
  have hdescent : baseEnd_4932153 < baseStart_4932153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932157 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 5]
def baseStart_4932157 : Nat := 118140960795 + 4932157 * 2 ^ 59
def prefixEnd_4932157 : Nat := 4983230072969 + 3 ^ 40 * 4932157 * 2
def baseEnd_4932157 : Nat := 281396356048618294083881

theorem tailTrace_4932157 : CollatzResearch.WordTrace tailWord_4932157 prefixEnd_4932157 281396356048618294083881 := by
  unfold tailWord_4932157
  simp only [CollatzResearch.WordTrace]
  refine ⟨179890544392645009198170725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119927029595096672798780483 179890544392645009198170725)
  ·
    refine ⟨33729477073620939224657011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179890544392645009198170725 33729477073620939224657011)
    ·
      refine ⟨50594215610431408836985517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33729477073620939224657011 50594215610431408836985517)
      ·
        refine ⟨18972830853911778313869569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50594215610431408836985517 18972830853911778313869569)
        ·
          refine ⟨14229623140433833735402177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18972830853911778313869569 14229623140433833735402177)
          ·
            refine ⟨10672217355325375301551633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14229623140433833735402177 10672217355325375301551633)
            ·
              refine ⟨8004163016494031476163725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10672217355325375301551633 8004163016494031476163725)
              ·
                refine ⟨3001561131185261803561397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8004163016494031476163725 3001561131185261803561397)
                ·
                  refine ⟨281396356048618294083881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3001561131185261803561397 281396356048618294083881)
                  ·
                    rfl

theorem cell23_4932157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_4932157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932157 prefixEnd_4932157 := by exact prefixLift 4932157
  have htrace : WordTrace (prefixWord ++ tailWord_4932157) baseStart_4932157 baseEnd_4932157 := by
    simpa [prefixWord, tailWord_4932157, baseEnd_4932157] using wordTrace_append hprefix tailTrace_4932157
  have hstable : (prefixWord ++ tailWord_4932157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932157).length < 2 ^ (prefixWord ++ tailWord_4932157).sum := by decide
  have hdescent : baseEnd_4932157 < baseStart_4932157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932234 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_4932234 : Nat := 118140960795 + 4932234 * 2 ^ 59
def prefixEnd_4932234 : Nat := 4983230072969 + 3 ^ 40 * 4932234 * 2
def baseEnd_4932234 : Nat := 844202247482653615164025

theorem tailTrace_4932234 : CollatzResearch.WordTrace tailWord_4932234 prefixEnd_4932234 844202247482653615164025 := by
  unfold tailWord_4932234
  simp only [CollatzResearch.WordTrace]
  refine ⟨44973338203341512837180939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119928901875577367565815837 44973338203341512837180939)
  ·
    refine ⟨67460007305012269255771409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44973338203341512837180939 67460007305012269255771409)
    ·
      refine ⟨50595005478759201941828557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67460007305012269255771409 50595005478759201941828557)
      ·
        refine ⟨18973127054534700728185709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50595005478759201941828557 18973127054534700728185709)
        ·
          refine ⟨7114922645450512773069641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18973127054534700728185709 7114922645450512773069641)
          ·
            refine ⟨5336191984087884579802231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7114922645450512773069641 5336191984087884579802231)
            ·
              refine ⟨8004287976131826869703347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336191984087884579802231 8004287976131826869703347)
              ·
                refine ⟨12006431964197740304555021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8004287976131826869703347 12006431964197740304555021)
                ·
                  refine ⟨4502411986574152614208133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12006431964197740304555021 4502411986574152614208133)
                  ·
                    refine ⟨844202247482653615164025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4502411986574152614208133 844202247482653615164025)
                    ·
                      rfl

theorem cell23_4932234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_4932234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932234 prefixEnd_4932234 := by exact prefixLift 4932234
  have htrace : WordTrace (prefixWord ++ tailWord_4932234) baseStart_4932234 baseEnd_4932234 := by
    simpa [prefixWord, tailWord_4932234, baseEnd_4932234] using wordTrace_append hprefix tailTrace_4932234
  have hstable : (prefixWord ++ tailWord_4932234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932234).length < 2 ^ (prefixWord ++ tailWord_4932234).sum := by decide
  have hdescent : baseEnd_4932234 < baseStart_4932234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932243 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 5, 5]
def baseStart_4932243 : Nat := 118140960795 + 4932243 * 2 ^ 59
def prefixEnd_4932243 : Nat := 4983230072969 + 3 ^ 40 * 4932243 * 2
def baseEnd_4932243 : Nat := 844203787924617103426511

theorem tailTrace_4932243 : CollatzResearch.WordTrace tailWord_4932243 prefixEnd_4932243 844203787924617103426511 := by
  unfold tailWord_4932243
  simp only [CollatzResearch.WordTrace]
  refine ⟨179893681070333445885801383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119929120713555630590534255 179893681070333445885801383)
  ·
    refine ⟨269840521605500168828702075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179893681070333445885801383 269840521605500168828702075)
    ·
      refine ⟨404760782408250253243053113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269840521605500168828702075 404760782408250253243053113)
      ·
        refine ⟨303570586806187689932289835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404760782408250253243053113 303570586806187689932289835)
        ·
          refine ⟨455355880209281534898434753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303570586806187689932289835 455355880209281534898434753)
          ·
            refine ⟨341516910156961151173826065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455355880209281534898434753 341516910156961151173826065)
            ·
              refine ⟨256137682617720863380369549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341516910156961151173826065 256137682617720863380369549)
              ·
                refine ⟨96051630981645323767638581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256137682617720863380369549 96051630981645323767638581)
                ·
                  refine ⟨9004840404529249103216117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96051630981645323767638581 9004840404529249103216117)
                  ·
                    refine ⟨844203787924617103426511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9004840404529249103216117 844203787924617103426511)
                    ·
                      rfl

theorem cell23_4932243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 5].length) (baseStart_4932243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932243 prefixEnd_4932243 := by exact prefixLift 4932243
  have htrace : WordTrace (prefixWord ++ tailWord_4932243) baseStart_4932243 baseEnd_4932243 := by
    simpa [prefixWord, tailWord_4932243, baseEnd_4932243] using wordTrace_append hprefix tailTrace_4932243
  have hstable : (prefixWord ++ tailWord_4932243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932243).length < 2 ^ (prefixWord ++ tailWord_4932243).sum := by decide
  have hdescent : baseEnd_4932243 < baseStart_4932243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932260 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_4932260 : Nat := 118140960795 + 4932260 * 2 ^ 59
def prefixEnd_4932260 : Nat := 4983230072969 + 3 ^ 40 * 4932260 * 2
def baseEnd_4932260 : Nat := 844206697648325914588985

theorem tailTrace_4932260 : CollatzResearch.WordTrace tailWord_4932260 prefixEnd_4932260 844206697648325914588985 := by
  unfold tailWord_4932260
  simp only [CollatzResearch.WordTrace]
  refine ⟨89947150555635928894585117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119929534074181238526113489 89947150555635928894585117)
  ·
    refine ⟨33730181458363473335469419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89947150555635928894585117 33730181458363473335469419)
    ·
      refine ⟨50595272187545210003204129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33730181458363473335469419 50595272187545210003204129)
      ·
        refine ⟨37946454140658907502403097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50595272187545210003204129 37946454140658907502403097)
        ·
          refine ⟨28459840605494180626802323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37946454140658907502403097 28459840605494180626802323)
          ·
            refine ⟨42689760908241270940203485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28459840605494180626802323 42689760908241270940203485)
            ·
              refine ⟨16008660340590476602576307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42689760908241270940203485 16008660340590476602576307)
              ·
                refine ⟨24012990510885714903864461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16008660340590476602576307 24012990510885714903864461)
                ·
                  refine ⟨9004871441582143088949173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24012990510885714903864461 9004871441582143088949173)
                  ·
                    refine ⟨844206697648325914588985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9004871441582143088949173 844206697648325914588985)
                    ·
                      rfl

theorem cell23_4932260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_4932260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932260 prefixEnd_4932260 := by exact prefixLift 4932260
  have htrace : WordTrace (prefixWord ++ tailWord_4932260) baseStart_4932260 baseEnd_4932260 := by
    simpa [prefixWord, tailWord_4932260, baseEnd_4932260] using wordTrace_append hprefix tailTrace_4932260
  have hstable : (prefixWord ++ tailWord_4932260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932260).length < 2 ^ (prefixWord ++ tailWord_4932260).sum := by decide
  have hdescent : baseEnd_4932260 < baseStart_4932260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_4932274 : Nat := 118140960795 + 4932274 * 2 ^ 59
def prefixEnd_4932274 : Nat := 4983230072969 + 3 ^ 40 * 4932274 * 2
def baseEnd_4932274 : Nat := 2532627281674140688991891

theorem tailTrace_4932274 : CollatzResearch.WordTrace tailWord_4932274 prefixEnd_4932274 2532627281674140688991891 := by
  unfold tailWord_4932274
  simp only [CollatzResearch.WordTrace]
  refine ⟨44973702933305284545044969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119929874488814092120119917 44973702933305284545044969)
  ·
    refine ⟨33730277199978963408783727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44973702933305284545044969 33730277199978963408783727)
    ·
      refine ⟨50595415799968445113175591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33730277199978963408783727 50595415799968445113175591)
      ·
        refine ⟨75893123699952667669763387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50595415799968445113175591 75893123699952667669763387)
        ·
          refine ⟨113839685549929001504645081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75893123699952667669763387 113839685549929001504645081)
          ·
            refine ⟨85379764162446751128483811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113839685549929001504645081 85379764162446751128483811)
            ·
              refine ⟨128069646243670126692725717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85379764162446751128483811 128069646243670126692725717)
              ·
                refine ⟨3001632333836018594360759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128069646243670126692725717 3001632333836018594360759)
                ·
                  refine ⟨4502448500754027891541139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3001632333836018594360759 4502448500754027891541139)
                  ·
                    refine ⟨6753672751131041837311709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502448500754027891541139 6753672751131041837311709)
                    ·
                      refine ⟨2532627281674140688991891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6753672751131041837311709 2532627281674140688991891)
                      ·
                        rfl

theorem cell23_4932274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_4932274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932274 prefixEnd_4932274 := by exact prefixLift 4932274
  have htrace : WordTrace (prefixWord ++ tailWord_4932274) baseStart_4932274 baseEnd_4932274 := by
    simpa [prefixWord, tailWord_4932274, baseEnd_4932274] using wordTrace_append hprefix tailTrace_4932274
  have hstable : (prefixWord ++ tailWord_4932274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932274).length < 2 ^ (prefixWord ++ tailWord_4932274).sum := by decide
  have hdescent : baseEnd_4932274 < baseStart_4932274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932297 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 9, 2, 2]
def baseStart_4932297 : Nat := 118140960795 + 4932297 * 2 ^ 59
def prefixEnd_4932297 : Nat := 4983230072969 + 3 ^ 40 * 4932297 * 2
def baseEnd_4932297 : Nat := 2532639091729194099004285

theorem tailTrace_4932297 : CollatzResearch.WordTrace tailWord_4932297 prefixEnd_4932297 2532639091729194099004285 := by
  unfold tailWord_4932297
  simp only [CollatzResearch.WordTrace]
  refine ⟨179895650612137813108267145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119930433741425208738844763 179895650612137813108267145)
  ·
    refine ⟨134921737959103359831200359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179895650612137813108267145 134921737959103359831200359)
    ·
      refine ⟨202382606938655039746800539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134921737959103359831200359 202382606938655039746800539)
      ·
        refine ⟨303573910407982559620200809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202382606938655039746800539 303573910407982559620200809)
        ·
          refine ⟨227680432805986919715150607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303573910407982559620200809 227680432805986919715150607)
          ·
            refine ⟨341520649208980379572725911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227680432805986919715150607 341520649208980379572725911)
            ·
              refine ⟨512280973813470569359088867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341520649208980379572725911 512280973813470569359088867)
              ·
                refine ⟨768421460720205854038633301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512280973813470569359088867 768421460720205854038633301)
                ·
                  refine ⟨4502469496407456176007617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 768421460720205854038633301 4502469496407456176007617)
                  ·
                    refine ⟨3376852122305592132005713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4502469496407456176007617 3376852122305592132005713)
                    ·
                      refine ⟨2532639091729194099004285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376852122305592132005713 2532639091729194099004285)
                      ·
                        rfl

theorem cell23_4932297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 2, 2].length) (baseStart_4932297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932297 prefixEnd_4932297 := by exact prefixLift 4932297
  have htrace : WordTrace (prefixWord ++ tailWord_4932297) baseStart_4932297 baseEnd_4932297 := by
    simpa [prefixWord, tailWord_4932297, baseEnd_4932297] using wordTrace_append hprefix tailTrace_4932297
  have hstable : (prefixWord ++ tailWord_4932297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932297).length < 2 ^ (prefixWord ++ tailWord_4932297).sum := by decide
  have hdescent : baseEnd_4932297 < baseStart_4932297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932314 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_4932314 : Nat := 118140960795 + 4932314 * 2 ^ 59
def prefixEnd_4932314 : Nat := 4983230072969 + 3 ^ 40 * 4932314 * 2
def baseEnd_4932314 : Nat := 2532647820900320532491707

theorem tailTrace_4932314 : CollatzResearch.WordTrace tailWord_4932314 prefixEnd_4932314 2532647820900320532491707 := by
  unfold tailWord_4932314
  simp only [CollatzResearch.WordTrace]
  refine ⟨44974067663269056252908999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119930847102050816674423997 44974067663269056252908999)
  ·
    refine ⟨67461101494903584379363499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44974067663269056252908999 67461101494903584379363499)
    ·
      refine ⟨101191652242355376569045249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67461101494903584379363499 101191652242355376569045249)
      ·
        refine ⟨75893739181766532426783937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101191652242355376569045249 75893739181766532426783937)
        ·
          refine ⟨56920304386324899320087953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75893739181766532426783937 56920304386324899320087953)
          ·
            refine ⟨42690228289743674490065965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56920304386324899320087953 42690228289743674490065965)
            ·
              refine ⟨16008835608653877933774737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42690228289743674490065965 16008835608653877933774737)
              ·
                refine ⟨12006626706490408450331053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16008835608653877933774737 12006626706490408450331053)
                ·
                  refine ⟨4502485014933903168874145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12006626706490408450331053 4502485014933903168874145)
                  ·
                    refine ⟨3376863761200427376655609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4502485014933903168874145 3376863761200427376655609)
                    ·
                      refine ⟨2532647820900320532491707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376863761200427376655609 2532647820900320532491707)
                      ·
                        rfl

theorem cell23_4932314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_4932314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932314 prefixEnd_4932314 := by exact prefixLift 4932314
  have htrace : WordTrace (prefixWord ++ tailWord_4932314) baseStart_4932314 baseEnd_4932314 := by
    simpa [prefixWord, tailWord_4932314, baseEnd_4932314] using wordTrace_append hprefix tailTrace_4932314
  have hstable : (prefixWord ++ tailWord_4932314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932314).length < 2 ^ (prefixWord ++ tailWord_4932314).sum := by decide
  have hdescent : baseEnd_4932314 < baseStart_4932314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932334 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_4932334 : Nat := 118140960795 + 4932334 * 2 ^ 59
def prefixEnd_4932334 : Nat := 4983230072969 + 3 ^ 40 * 4932334 * 2
def baseEnd_4932334 : Nat := 2532658090513410454241615

theorem tailTrace_4932334 : CollatzResearch.WordTrace tailWord_4932334 prefixEnd_4932334 2532658090513410454241615 := by
  unfold tailWord_4932334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487125014125471053420507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119931333408669178951576037 22487125014125471053420507)
  ·
    refine ⟨33730687521188206580130761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22487125014125471053420507 33730687521188206580130761)
    ·
      refine ⟨25298015640891154935098071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33730687521188206580130761 25298015640891154935098071)
      ·
        refine ⟨37947023461336732402647107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25298015640891154935098071 37947023461336732402647107)
        ·
          refine ⟨56920535192005098603970661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37947023461336732402647107 56920535192005098603970661)
          ·
            refine ⟨10672600348500955988244499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56920535192005098603970661 10672600348500955988244499)
            ·
              refine ⟨16008900522751433982366749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10672600348500955988244499 16008900522751433982366749)
              ·
                refine ⟨6003337696031787743387531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16008900522751433982366749 6003337696031787743387531)
                ·
                  refine ⟨9005006544047681615081297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003337696031787743387531 9005006544047681615081297)
                  ·
                    refine ⟨6753754908035761211310973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9005006544047681615081297 6753754908035761211310973)
                    ·
                      refine ⟨2532658090513410454241615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6753754908035761211310973 2532658090513410454241615)
                      ·
                        rfl

theorem cell23_4932334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_4932334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932334 prefixEnd_4932334 := by exact prefixLift 4932334
  have htrace : WordTrace (prefixWord ++ tailWord_4932334) baseStart_4932334 baseEnd_4932334 := by
    simpa [prefixWord, tailWord_4932334, baseEnd_4932334] using wordTrace_append hprefix tailTrace_4932334
  have hstable : (prefixWord ++ tailWord_4932334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932334).length < 2 ^ (prefixWord ++ tailWord_4932334).sum := by decide
  have hdescent : baseEnd_4932334 < baseStart_4932334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932357 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_4932357 : Nat := 118140960795 + 4932357 * 2 ^ 59
def prefixEnd_4932357 : Nat := 4983230072969 + 3 ^ 40 * 4932357 * 2
def baseEnd_4932357 : Nat := 2532669900568463864254009

theorem tailTrace_4932357 : CollatzResearch.WordTrace tailWord_4932357 prefixEnd_4932357 2532669900568463864254009 := by
  unfold tailWord_4932357
  simp only [CollatzResearch.WordTrace]
  refine ⟨179897838991920443355451325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119931892661280295570300883 179897838991920443355451325)
  ·
    refine ⟨67461689621970166258294247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179897838991920443355451325 67461689621970166258294247)
    ·
      refine ⟨101192534432955249387441371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67461689621970166258294247 101192534432955249387441371)
      ·
        refine ⟨151788801649432874081162057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101192534432955249387441371 151788801649432874081162057)
        ·
          refine ⟨113841601237074655560871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151788801649432874081162057 113841601237074655560871543)
          ·
            refine ⟨170762401855611983341307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113841601237074655560871543 170762401855611983341307315)
            ·
              refine ⟨256143602783417975011960973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170762401855611983341307315 256143602783417975011960973)
              ·
                refine ⟨96053851043781740629485365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256143602783417975011960973 96053851043781740629485365)
                ·
                  refine ⟨9005048535354538184014253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96053851043781740629485365 9005048535354538184014253)
                  ·
                    refine ⟨3376893200757951819005345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9005048535354538184014253 3376893200757951819005345)
                    ·
                      refine ⟨2532669900568463864254009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376893200757951819005345 2532669900568463864254009)
                      ·
                        rfl

theorem cell23_4932357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_4932357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932357 prefixEnd_4932357 := by exact prefixLift 4932357
  have htrace : WordTrace (prefixWord ++ tailWord_4932357) baseStart_4932357 baseEnd_4932357 := by
    simpa [prefixWord, tailWord_4932357, baseEnd_4932357] using wordTrace_append hprefix tailTrace_4932357
  have hstable : (prefixWord ++ tailWord_4932357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932357).length < 2 ^ (prefixWord ++ tailWord_4932357).sum := by decide
  have hdescent : baseEnd_4932357 < baseStart_4932357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932387 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 3, 4, 2]
def baseStart_4932387 : Nat := 118140960795 + 4932387 * 2 ^ 59
def prefixEnd_4932387 : Nat := 4983230072969 + 3 ^ 40 * 4932387 * 2
def baseEnd_4932387 : Nat := 2532685304988098746878871

theorem tailTrace_4932387 : CollatzResearch.WordTrace tailWord_4932387 prefixEnd_4932387 2532685304988098746878871 := by
  unfold tailWord_4932387
  simp only [CollatzResearch.WordTrace]
  refine ⟨179898933181811758479043415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119932622121207838986028943 179898933181811758479043415)
  ·
    refine ⟨269848399772717637718565123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179898933181811758479043415 269848399772717637718565123)
    ·
      refine ⟨404772599659076456577847685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269848399772717637718565123 404772599659076456577847685)
      ·
        refine ⟨75894862436076835608346441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 404772599659076456577847685 75894862436076835608346441)
        ·
          refine ⟨56921146827057626706259831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75894862436076835608346441 56921146827057626706259831)
          ·
            refine ⟨85381720240586440059389747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56921146827057626706259831 85381720240586440059389747)
            ·
              refine ⟨128072580360879660089084621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85381720240586440059389747 128072580360879660089084621)
              ·
                refine ⟨48027217635329872533406733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128072580360879660089084621 48027217635329872533406733)
                ·
                  refine ⟨18010206613248702200027525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48027217635329872533406733 18010206613248702200027525)
                  ·
                    refine ⟨3376913739984131662505161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18010206613248702200027525 3376913739984131662505161)
                    ·
                      refine ⟨2532685304988098746878871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3376913739984131662505161 2532685304988098746878871)
                      ·
                        rfl

theorem cell23_4932387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_4932387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932387 prefixEnd_4932387 := by exact prefixLift 4932387
  have htrace : WordTrace (prefixWord ++ tailWord_4932387) baseStart_4932387 baseEnd_4932387 := by
    simpa [prefixWord, tailWord_4932387, baseEnd_4932387] using wordTrace_append hprefix tailTrace_4932387
  have hstable : (prefixWord ++ tailWord_4932387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932387).length < 2 ^ (prefixWord ++ tailWord_4932387).sum := by decide
  have hdescent : baseEnd_4932387 < baseStart_4932387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932400 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_4932400 : Nat := 118140960795 + 4932400 * 2 ^ 59
def prefixEnd_4932400 : Nat := 4983230072969 + 3 ^ 40 * 4932400 * 2
def baseEnd_4932400 : Nat := 2532691980236607196016311

theorem tailTrace_4932400 : CollatzResearch.WordTrace tailWord_4932400 prefixEnd_4932400 2532691980236607196016311 := by
  unfold tailWord_4932400
  simp only [CollatzResearch.WordTrace]
  refine ⟨89949703665382330849633327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119932938220509774466177769 89949703665382330849633327)
  ·
    refine ⟨134924555498073496274449991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89949703665382330849633327 134924555498073496274449991)
    ·
      refine ⟨202386833247110244411674987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134924555498073496274449991 202386833247110244411674987)
      ·
        refine ⟨303580249870665366617512481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202386833247110244411674987 303580249870665366617512481)
        ·
          refine ⟨227685187402999024963134361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303580249870665366617512481 227685187402999024963134361)
          ·
            refine ⟨170763890552249268722350771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227685187402999024963134361 170763890552249268722350771)
            ·
              refine ⟨256145835828373903083526157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170763890552249268722350771 256145835828373903083526157)
              ·
                refine ⟨96054688435640213656322309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256145835828373903083526157 96054688435640213656322309)
                ·
                  refine ⟨18010254081682540060560433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96054688435640213656322309 18010254081682540060560433)
                  ·
                    refine ⟨13507690561261905045420325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18010254081682540060560433 13507690561261905045420325)
                    ·
                      refine ⟨2532691980236607196016311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13507690561261905045420325 2532691980236607196016311)
                      ·
                        rfl

theorem cell23_4932400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_4932400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932400 prefixEnd_4932400 := by exact prefixLift 4932400
  have htrace : WordTrace (prefixWord ++ tailWord_4932400) baseStart_4932400 baseEnd_4932400 := by
    simpa [prefixWord, tailWord_4932400, baseEnd_4932400] using wordTrace_append hprefix tailTrace_4932400
  have hstable : (prefixWord ++ tailWord_4932400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932400).length < 2 ^ (prefixWord ++ tailWord_4932400).sum := by decide
  have hdescent : baseEnd_4932400 < baseStart_4932400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932430 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4932430 : Nat := 118140960795 + 4932430 * 2 ^ 59
def prefixEnd_4932430 : Nat := 4983230072969 + 3 ^ 40 * 4932430 * 2
def baseEnd_4932430 : Nat := 2532707384656242078641173

theorem tailTrace_4932430 : CollatzResearch.WordTrace tailWord_4932430 prefixEnd_4932430 2532707384656242078641173 := by
  unfold tailWord_4932430
  simp only [CollatzResearch.WordTrace]
  refine ⟨22487562690081997102857343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119933667680437317881905829 22487562690081997102857343)
  ·
    refine ⟨33731344035122995654286015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22487562690081997102857343 33731344035122995654286015)
    ·
      refine ⟨50597016052684493481429023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33731344035122995654286015 50597016052684493481429023)
      ·
        refine ⟨75895524079026740222143535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50597016052684493481429023 75895524079026740222143535)
        ·
          refine ⟨113843286118540110333215303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75895524079026740222143535 113843286118540110333215303)
          ·
            refine ⟨170764929177810165499822955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113843286118540110333215303 170764929177810165499822955)
            ·
              refine ⟨256147393766715248249734433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170764929177810165499822955 256147393766715248249734433)
              ·
                refine ⟨192110545325036436187300825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256147393766715248249734433 192110545325036436187300825)
                ·
                  refine ⟨144082908993777327140475619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192110545325036436187300825 144082908993777327140475619)
                  ·
                    refine ⟨216124363490665990710713429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144082908993777327140475619 216124363490665990710713429)
                    ·
                      refine ⟨2532707384656242078641173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 216124363490665990710713429 2532707384656242078641173)
                      ·
                        rfl

theorem cell23_4932430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4932430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932430 prefixEnd_4932430 := by exact prefixLift 4932430
  have htrace : WordTrace (prefixWord ++ tailWord_4932430) baseStart_4932430 baseEnd_4932430 := by
    simpa [prefixWord, tailWord_4932430, baseEnd_4932430] using wordTrace_append hprefix tailTrace_4932430
  have hstable : (prefixWord ++ tailWord_4932430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932430).length < 2 ^ (prefixWord ++ tailWord_4932430).sum := by decide
  have hdescent : baseEnd_4932430 < baseStart_4932430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932440 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_4932440 : Nat := 118140960795 + 4932440 * 2 ^ 59
def prefixEnd_4932440 : Nat := 4983230072969 + 3 ^ 40 * 4932440 * 2
def baseEnd_4932440 : Nat := 844237506487595679838709

theorem tailTrace_4932440 : CollatzResearch.WordTrace tailWord_4932440 prefixEnd_4932440 844237506487595679838709 := by
  unfold tailWord_4932440
  simp only [CollatzResearch.WordTrace]
  refine ⟨89950433125309874265361387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119933910833746499020481849 89950433125309874265361387)
  ·
    refine ⟨134925649687964811398042081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89950433125309874265361387 134925649687964811398042081)
    ·
      refine ⟨101194237265973608548531561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134925649687964811398042081 101194237265973608548531561)
      ·
        refine ⟨75895677949480206411398671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101194237265973608548531561 75895677949480206411398671)
        ·
          refine ⟨113843516924220309617098007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75895677949480206411398671 113843516924220309617098007)
          ·
            refine ⟨170765275386330464425647011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113843516924220309617098007 170765275386330464425647011)
            ·
              refine ⟨256147913079495696638470517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170765275386330464425647011 256147913079495696638470517)
              ·
                refine ⟨24013866851202721559856611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256147913079495696638470517 24013866851202721559856611)
                ·
                  refine ⟨36020800276804082339784917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24013866851202721559856611 36020800276804082339784917)
                  ·
                    refine ⟨844237506487595679838709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36020800276804082339784917 844237506487595679838709)
                    ·
                      rfl

theorem cell23_4932440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_4932440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932440 prefixEnd_4932440 := by exact prefixLift 4932440
  have htrace : WordTrace (prefixWord ++ tailWord_4932440) baseStart_4932440 baseEnd_4932440 := by
    simpa [prefixWord, tailWord_4932440, baseEnd_4932440] using wordTrace_append hprefix tailTrace_4932440
  have hstable : (prefixWord ++ tailWord_4932440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932440).length < 2 ^ (prefixWord ++ tailWord_4932440).sum := by decide
  have hdescent : baseEnd_4932440 < baseStart_4932440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932477 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_4932477 : Nat := 118140960795 + 4932477 * 2 ^ 59
def prefixEnd_4932477 : Nat := 4983230072969 + 3 ^ 40 * 4932477 * 2
def baseEnd_4932477 : Nat := 2532731518247003394753457

theorem tailTrace_4932477 : CollatzResearch.WordTrace tailWord_4932477 prefixEnd_4932477 2532731518247003394753457 := by
  unfold tailWord_4932477
  simp only [CollatzResearch.WordTrace]
  refine ⟨179902215751485703849819685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119934810500990469233213123 179902215751485703849819685)
  ·
    refine ⟨33731665453403569471841191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179902215751485703849819685 33731665453403569471841191)
    ·
      refine ⟨50597498180105354207761787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33731665453403569471841191 50597498180105354207761787)
      ·
        refine ⟨75896247270158031311642681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50597498180105354207761787 75896247270158031311642681)
        ·
          refine ⟨56922185452618523483732011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75896247270158031311642681 56922185452618523483732011)
          ·
            refine ⟨85383278178927785225598017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56922185452618523483732011 85383278178927785225598017)
            ·
              refine ⟨64037458634195838919198513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85383278178927785225598017 64037458634195838919198513)
              ·
                refine ⟨48028093975646879189398885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64037458634195838919198513 48028093975646879189398885)
                ·
                  refine ⟨9005267620433789848012291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48028093975646879189398885 9005267620433789848012291)
                  ·
                    refine ⟨13507901430650684772018437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9005267620433789848012291 13507901430650684772018437)
                    ·
                      refine ⟨2532731518247003394753457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13507901430650684772018437 2532731518247003394753457)
                      ·
                        rfl

theorem cell23_4932477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_4932477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932477 prefixEnd_4932477 := by exact prefixLift 4932477
  have htrace : WordTrace (prefixWord ++ tailWord_4932477) baseStart_4932477 baseEnd_4932477 := by
    simpa [prefixWord, tailWord_4932477, baseEnd_4932477] using wordTrace_append hprefix tailTrace_4932477
  have hstable : (prefixWord ++ tailWord_4932477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932477).length < 2 ^ (prefixWord ++ tailWord_4932477).sum := by decide
  have hdescent : baseEnd_4932477 < baseStart_4932477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932587 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3]
def baseStart_4932587 : Nat := 118140960795 + 4932587 * 2 ^ 59
def prefixEnd_4932587 : Nat := 4983230072969 + 3 ^ 40 * 4932587 * 2
def baseEnd_4932587 : Nat := 2532788001118997964377951

theorem tailTrace_4932587 : CollatzResearch.WordTrace tailWord_4932587 prefixEnd_4932587 2532788001118997964377951 := by
  unfold tailWord_4932587
  simp only [CollatzResearch.WordTrace]
  refine ⟨179906227781087192636324015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119937485187391461757549343 179906227781087192636324015)
  ·
    refine ⟨269859341671630788954486023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179906227781087192636324015 269859341671630788954486023)
    ·
      refine ⟨404789012507446183431729035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269859341671630788954486023 404789012507446183431729035)
      ·
        refine ⟨607183518761169275147593553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404789012507446183431729035 607183518761169275147593553)
        ·
          refine ⟨455387639070876956360695165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607183518761169275147593553 455387639070876956360695165)
          ·
            refine ⟨170770364651578858635260687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455387639070876956360695165 170770364651578858635260687)
            ·
              refine ⟨256155546977368287952891031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170770364651578858635260687 256155546977368287952891031)
              ·
                refine ⟨384233320466052431929336547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256155546977368287952891031 384233320466052431929336547)
                ·
                  refine ⟨576349980699078647894004821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384233320466052431929336547 576349980699078647894004821)
                  ·
                    refine ⟨6754101336317327905007869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 576349980699078647894004821 6754101336317327905007869)
                    ·
                      refine ⟨2532788001118997964377951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754101336317327905007869 2532788001118997964377951)
                      ·
                        rfl

theorem cell23_4932587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3].length) (baseStart_4932587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932587 prefixEnd_4932587 := by exact prefixLift 4932587
  have htrace : WordTrace (prefixWord ++ tailWord_4932587) baseStart_4932587 baseEnd_4932587 := by
    simpa [prefixWord, tailWord_4932587, baseEnd_4932587] using wordTrace_append hprefix tailTrace_4932587
  have hstable : (prefixWord ++ tailWord_4932587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932587).length < 2 ^ (prefixWord ++ tailWord_4932587).sum := by decide
  have hdescent : baseEnd_4932587 < baseStart_4932587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932598 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_4932598 : Nat := 118140960795 + 4932598 * 2 ^ 59
def prefixEnd_4932598 : Nat := 4983230072969 + 3 ^ 40 * 4932598 * 2
def baseEnd_4932598 : Nat := 844264549802065807113467

theorem tailTrace_4932598 : CollatzResearch.WordTrace tailWord_4932598 prefixEnd_4932598 844264549802065807113467 := by
  unfold tailWord_4932598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244164311502958844685903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119937752656031561009982965 11244164311502958844685903)
  ·
    refine ⟨16866246467254438267028855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11244164311502958844685903 16866246467254438267028855)
    ·
      refine ⟨25299369700881657400543283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16866246467254438267028855 25299369700881657400543283)
      ·
        refine ⟨37949054551322486100814925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25299369700881657400543283 37949054551322486100814925)
        ·
          refine ⟨14230895456745932287805597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37949054551322486100814925 14230895456745932287805597)
          ·
            refine ⟨5336585796279724607927099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14230895456745932287805597 5336585796279724607927099)
            ·
              refine ⟨8004878694419586911890649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336585796279724607927099 8004878694419586911890649)
              ·
                refine ⟨6003659020814690183917987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8004878694419586911890649 6003659020814690183917987)
                ·
                  refine ⟨9005488531222035275876981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003659020814690183917987 9005488531222035275876981)
                  ·
                    refine ⟨844264549802065807113467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9005488531222035275876981 844264549802065807113467)
                    ·
                      rfl

theorem cell23_4932598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_4932598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932598 prefixEnd_4932598 := by exact prefixLift 4932598
  have htrace : WordTrace (prefixWord ++ tailWord_4932598) baseStart_4932598 baseEnd_4932598 := by
    simpa [prefixWord, tailWord_4932598, baseEnd_4932598] using wordTrace_append hprefix tailTrace_4932598
  have hstable : (prefixWord ++ tailWord_4932598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932598).length < 2 ^ (prefixWord ++ tailWord_4932598).sum := by decide
  have hdescent : baseEnd_4932598 < baseStart_4932598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932601 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 5, 2, 2]
def baseStart_4932601 : Nat := 118140960795 + 4932601 * 2 ^ 59
def prefixEnd_4932601 : Nat := 4983230072969 + 3 ^ 40 * 4932601 * 2
def baseEnd_4932601 : Nat := 2532795189848160909602887

theorem tailTrace_4932601 : CollatzResearch.WordTrace tailWord_4932601 prefixEnd_4932601 2532795189848160909602887 := by
  unfold tailWord_4932601
  simp only [CollatzResearch.WordTrace]
  refine ⟨179906738403036473027333657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119937825602024315351555771 179906738403036473027333657)
  ·
    refine ⟨134930053802277354770500243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179906738403036473027333657 134930053802277354770500243)
    ·
      refine ⟨202395080703416032155750365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134930053802277354770500243 202395080703416032155750365)
      ·
        refine ⟨75898155263781012058406387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202395080703416032155750365 75898155263781012058406387)
        ·
          refine ⟨113847232895671518087609581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75898155263781012058406387 113847232895671518087609581)
          ·
            refine ⟨42692712335876819282853593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113847232895671518087609581 42692712335876819282853593)
            ·
              refine ⟨32019534251907614462140195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42692712335876819282853593 32019534251907614462140195)
              ·
                refine ⟨48029301377861421693210293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32019534251907614462140195 48029301377861421693210293)
                ·
                  refine ⟨4502747004174508283738465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48029301377861421693210293 4502747004174508283738465)
                  ·
                    refine ⟨3377060253130881212803849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4502747004174508283738465 3377060253130881212803849)
                    ·
                      refine ⟨2532795189848160909602887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377060253130881212803849 2532795189848160909602887)
                      ·
                        rfl

theorem cell23_4932601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_4932601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932601 prefixEnd_4932601 := by exact prefixLift 4932601
  have htrace : WordTrace (prefixWord ++ tailWord_4932601) baseStart_4932601 baseEnd_4932601 := by
    simpa [prefixWord, tailWord_4932601, baseEnd_4932601] using wordTrace_append hprefix tailTrace_4932601
  have hstable : (prefixWord ++ tailWord_4932601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932601).length < 2 ^ (prefixWord ++ tailWord_4932601).sum := by decide
  have hdescent : baseEnd_4932601 < baseStart_4932601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932618 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_4932618 : Nat := 118140960795 + 4932618 * 2 ^ 59
def prefixEnd_4932618 : Nat := 4983230072969 + 3 ^ 40 * 4932618 * 2
def baseEnd_4932618 : Nat := 2532803919019287343090309

theorem tailTrace_4932618 : CollatzResearch.WordTrace tailWord_4932618 prefixEnd_4932618 2532803919019287343090309 := by
  unfold tailWord_4932618
  simp only [CollatzResearch.WordTrace]
  refine ⟨44976839610993721232675627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119938238962649923287135005 44976839610993721232675627)
  ·
    refine ⟨67465259416490581849013441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44976839610993721232675627 67465259416490581849013441)
    ·
      refine ⟨50598944562367936386760081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67465259416490581849013441 50598944562367936386760081)
      ·
        refine ⟨37949208421775952290070061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50598944562367936386760081 37949208421775952290070061)
        ·
          refine ⟨14230953158165982108776273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37949208421775952290070061 14230953158165982108776273)
          ·
            refine ⟨10673214868624486581582205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14230953158165982108776273 10673214868624486581582205)
            ·
              refine ⟨4002455575734182468093327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10673214868624486581582205 4002455575734182468093327)
              ·
                refine ⟨6003683363601273702139991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002455575734182468093327 6003683363601273702139991)
                ·
                  refine ⟨9005525045401910553209987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003683363601273702139991 9005525045401910553209987)
                  ·
                    refine ⟨13508287568102865829814981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9005525045401910553209987 13508287568102865829814981)
                    ·
                      refine ⟨2532803919019287343090309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13508287568102865829814981 2532803919019287343090309)
                      ·
                        rfl

theorem cell23_4932618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_4932618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932618 prefixEnd_4932618 := by exact prefixLift 4932618
  have htrace : WordTrace (prefixWord ++ tailWord_4932618) baseStart_4932618 baseEnd_4932618 := by
    simpa [prefixWord, tailWord_4932618, baseEnd_4932618] using wordTrace_append hprefix tailTrace_4932618
  have hstable : (prefixWord ++ tailWord_4932618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932618).length < 2 ^ (prefixWord ++ tailWord_4932618).sum := by decide
  have hdescent : baseEnd_4932618 < baseStart_4932618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932634 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_4932634 : Nat := 118140960795 + 4932634 * 2 ^ 59
def prefixEnd_4932634 : Nat := 4983230072969 + 3 ^ 40 * 4932634 * 2
def baseEnd_4932634 : Nat := 2532812134709759280490235

theorem tailTrace_4932634 : CollatzResearch.WordTrace tailWord_4932634 prefixEnd_4932634 2532812134709759280490235 := by
  unfold tailWord_4932634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44976985502979229915821239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119938628007944613108856637 44976985502979229915821239)
  ·
    refine ⟨67465478254468844873731859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44976985502979229915821239 67465478254468844873731859)
    ·
      refine ⟨101198217381703267310597789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67465478254468844873731859 101198217381703267310597789)
      ·
        refine ⟨37949331518138725241474171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101198217381703267310597789 37949331518138725241474171)
        ·
          refine ⟨56923997277208087862211257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37949331518138725241474171 56923997277208087862211257)
          ·
            refine ⟨42692997957906065896658443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56923997277208087862211257 42692997957906065896658443)
            ·
              refine ⟨64039496936859098844987665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42692997957906065896658443 64039496936859098844987665)
              ·
                refine ⟨48029622702644324133740749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64039496936859098844987665 48029622702644324133740749)
                ·
                  refine ⟨18011108513491621550152781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48029622702644324133740749 18011108513491621550152781)
                  ·
                    refine ⟨6754165692559358081307293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18011108513491621550152781 6754165692559358081307293)
                    ·
                      refine ⟨2532812134709759280490235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754165692559358081307293 2532812134709759280490235)
                      ·
                        rfl

theorem cell23_4932634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_4932634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932634 prefixEnd_4932634 := by exact prefixLift 4932634
  have htrace : WordTrace (prefixWord ++ tailWord_4932634) baseStart_4932634 baseEnd_4932634 := by
    simpa [prefixWord, tailWord_4932634, baseEnd_4932634] using wordTrace_append hprefix tailTrace_4932634
  have hstable : (prefixWord ++ tailWord_4932634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932634).length < 2 ^ (prefixWord ++ tailWord_4932634).sum := by decide
  have hdescent : baseEnd_4932634 < baseStart_4932634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932651 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 3]
def baseStart_4932651 : Nat := 118140960795 + 4932651 * 2 ^ 59
def prefixEnd_4932651 : Nat := 4983230072969 + 3 ^ 40 * 4932651 * 2
def baseEnd_4932651 : Nat := 2532820863880885713977657

theorem tailTrace_4932651 : CollatzResearch.WordTrace tailWord_4932651 prefixEnd_4932651 2532820863880885713977657 := by
  unfold tailWord_4932651
  simp only [CollatzResearch.WordTrace]
  refine ⟨179908562052855331566653807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119939041368570221044435871 179908562052855331566653807)
  ·
    refine ⟨269862843079282997349980711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179908562052855331566653807 269862843079282997349980711)
    ·
      refine ⟨404794264618924496024971067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269862843079282997349980711 404794264618924496024971067)
      ·
        refine ⟨607191396928386744037456601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404794264618924496024971067 607191396928386744037456601)
        ·
          refine ⟨455393547696290058028092451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607191396928386744037456601 455393547696290058028092451)
          ·
            refine ⟨683090321544435087042138677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455393547696290058028092451 683090321544435087042138677)
            ·
              refine ⟨64039717644790789410200501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 683090321544435087042138677 64039717644790789410200501)
              ·
                refine ⟨6003723529199136507206297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64039717644790789410200501 6003723529199136507206297)
                ·
                  refine ⟨4502792646899352380404723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6003723529199136507206297 4502792646899352380404723)
                  ·
                    refine ⟨6754188970349028570607085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502792646899352380404723 6754188970349028570607085)
                    ·
                      refine ⟨2532820863880885713977657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754188970349028570607085 2532820863880885713977657)
                      ·
                        rfl

theorem cell23_4932651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 3].length) (baseStart_4932651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932651 prefixEnd_4932651 := by exact prefixLift 4932651
  have htrace : WordTrace (prefixWord ++ tailWord_4932651) baseStart_4932651 baseEnd_4932651 := by
    simpa [prefixWord, tailWord_4932651, baseEnd_4932651] using wordTrace_append hprefix tailTrace_4932651
  have hstable : (prefixWord ++ tailWord_4932651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932651).length < 2 ^ (prefixWord ++ tailWord_4932651).sum := by decide
  have hdescent : baseEnd_4932651 < baseStart_4932651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932654 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4932654 : Nat := 118140960795 + 4932654 * 2 ^ 59
def prefixEnd_4932654 : Nat := 4983230072969 + 3 ^ 40 * 4932654 * 2
def baseEnd_4932654 : Nat := 844274134774283067413381

theorem tailTrace_4932654 : CollatzResearch.WordTrace tailWord_4932654 prefixEnd_4932654 844274134774283067413381 := by
  unfold tailWord_4932654
  simp only [CollatzResearch.WordTrace]
  refine ⟨22488583933980557884876627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119939114314562975386008677 22488583933980557884876627)
  ·
    refine ⟨33732875900970836827314941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22488583933980557884876627 33732875900970836827314941)
    ·
      refine ⟨12649828462864063810243103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33732875900970836827314941 12649828462864063810243103)
      ·
        refine ⟨18974742694296095715364655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12649828462864063810243103 18974742694296095715364655)
        ·
          refine ⟨28462114041444143573046983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18974742694296095715364655 28462114041444143573046983)
          ·
            refine ⟨42693171062166215359570475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28462114041444143573046983 42693171062166215359570475)
            ·
              refine ⟨64039756593249323039355713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42693171062166215359570475 64039756593249323039355713)
              ·
                refine ⟨48029817444936992279516785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64039756593249323039355713 48029817444936992279516785)
                ·
                  refine ⟨36022363083702744209637589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48029817444936992279516785 36022363083702744209637589)
                  ·
                    refine ⟨844274134774283067413381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36022363083702744209637589 844274134774283067413381)
                    ·
                      rfl

theorem cell23_4932654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4932654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932654 prefixEnd_4932654 := by exact prefixLift 4932654
  have htrace : WordTrace (prefixWord ++ tailWord_4932654) baseStart_4932654 baseEnd_4932654 := by
    simpa [prefixWord, tailWord_4932654, baseEnd_4932654] using wordTrace_append hprefix tailTrace_4932654
  have hstable : (prefixWord ++ tailWord_4932654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932654).length < 2 ^ (prefixWord ++ tailWord_4932654).sum := by decide
  have hdescent : baseEnd_4932654 < baseStart_4932654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932667 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 6, 6]
def baseStart_4932667 : Nat := 118140960795 + 4932667 * 2 ^ 59
def prefixEnd_4932667 : Nat := 4983230072969 + 3 ^ 40 * 4932667 * 2
def baseEnd_4932667 : Nat := 844276359857119217125861

theorem tailTrace_4932667 : CollatzResearch.WordTrace tailWord_4932667 prefixEnd_4932667 844276359857119217125861 := by
  unfold tailWord_4932667
  simp only [CollatzResearch.WordTrace]
  refine ⟨179909145620797366299236255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119939430413864910866157503 179909145620797366299236255)
  ·
    refine ⟨269863718431196049448854383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179909145620797366299236255 269863718431196049448854383)
    ·
      refine ⟨404795577646794074173281575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269863718431196049448854383 404795577646794074173281575)
      ·
        refine ⟨607193366470191111259922363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404795577646794074173281575 607193366470191111259922363)
        ·
          refine ⟨910790049705286666889883545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607193366470191111259922363 910790049705286666889883545)
          ·
            refine ⟨683092537278965000167412659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910790049705286666889883545 683092537278965000167412659)
            ·
              refine ⟨1024638805918447500251118989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683092537278965000167412659 1024638805918447500251118989)
              ·
                refine ⟨384239552219417812594169621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1024638805918447500251118989 384239552219417812594169621)
                ·
                  refine ⟨18011229010285209965351701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 384239552219417812594169621 18011229010285209965351701)
                  ·
                    refine ⟨844276359857119217125861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18011229010285209965351701 844276359857119217125861)
                    ·
                      rfl

theorem cell23_4932667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_4932667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932667 prefixEnd_4932667 := by exact prefixLift 4932667
  have htrace : WordTrace (prefixWord ++ tailWord_4932667) baseStart_4932667 baseEnd_4932667 := by
    simpa [prefixWord, tailWord_4932667, baseEnd_4932667] using wordTrace_append hprefix tailTrace_4932667
  have hstable : (prefixWord ++ tailWord_4932667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932667).length < 2 ^ (prefixWord ++ tailWord_4932667).sum := by decide
  have hdescent : baseEnd_4932667 < baseStart_4932667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932685 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4932685 : Nat := 118140960795 + 4932685 * 2 ^ 59
def prefixEnd_4932685 : Nat := 4983230072969 + 3 ^ 40 * 4932685 * 2
def baseEnd_4932685 : Nat := 2532838322223138580952501

theorem tailTrace_4932685 : CollatzResearch.WordTrace tailWord_4932685 prefixEnd_4932685 2532838322223138580952501 := by
  unfold tailWord_4932685
  simp only [CollatzResearch.WordTrace]
  refine ⟨179909802134732155373391509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119939868089821436915594339 179909802134732155373391509)
  ·
    refine ⟨8433271975065569783127727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 179909802134732155373391509 8433271975065569783127727)
    ·
      refine ⟨12649907962598354674691591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8433271975065569783127727 12649907962598354674691591)
      ·
        refine ⟨18974861943897532012037387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12649907962598354674691591 18974861943897532012037387)
        ·
          refine ⟨28462292915846298018056081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18974861943897532012037387 28462292915846298018056081)
          ·
            refine ⟨21346719686884723513542061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28462292915846298018056081 21346719686884723513542061)
            ·
              refine ⟨8005019882581771317578273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21346719686884723513542061 8005019882581771317578273)
              ·
                refine ⟨6003764911936328488183705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8005019882581771317578273 6003764911936328488183705)
                ·
                  refine ⟨4502823683952246366137779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6003764911936328488183705 4502823683952246366137779)
                  ·
                    refine ⟨6754235525928369549206669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502823683952246366137779 6754235525928369549206669)
                    ·
                      refine ⟨2532838322223138580952501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754235525928369549206669 2532838322223138580952501)
                      ·
                        rfl

theorem cell23_4932685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4932685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932685 prefixEnd_4932685 := by exact prefixLift 4932685
  have htrace : WordTrace (prefixWord ++ tailWord_4932685) baseStart_4932685 baseEnd_4932685 := by
    simpa [prefixWord, tailWord_4932685, baseEnd_4932685] using wordTrace_append hprefix tailTrace_4932685
  have hstable : (prefixWord ++ tailWord_4932685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932685).length < 2 ^ (prefixWord ++ tailWord_4932685).sum := by decide
  have hdescent : baseEnd_4932685 < baseStart_4932685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932687 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_4932687 : Nat := 118140960795 + 4932687 * 2 ^ 59
def prefixEnd_4932687 : Nat := 4983230072969 + 3 ^ 40 * 4932687 * 2
def baseEnd_4932687 : Nat := 2532839349184447573127491

theorem tailTrace_4932687 : CollatzResearch.WordTrace tailWord_4932687 prefixEnd_4932687 2532839349184447573127491 := by
  unfold tailWord_4932687
  simp only [CollatzResearch.WordTrace]
  refine ⟨179909875080724909714964315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119939916720483273143309543 179909875080724909714964315)
  ·
    refine ⟨269864812621087364572446473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179909875080724909714964315 269864812621087364572446473)
    ·
      refine ⟨202398609465815523429334855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269864812621087364572446473 202398609465815523429334855)
      ·
        refine ⟨303597914198723285144002283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202398609465815523429334855 303597914198723285144002283)
        ·
          refine ⟨455396871298084927716003425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303597914198723285144002283 455396871298084927716003425)
          ·
            refine ⟨341547653473563695787002569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455396871298084927716003425 341547653473563695787002569)
            ·
              refine ⟨256160740105172771840251927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341547653473563695787002569 256160740105172771840251927)
              ·
                refine ⟨384241110157759157760377891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256160740105172771840251927 384241110157759157760377891)
                ·
                  refine ⟨576361665236638736640566837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384241110157759157760377891 576361665236638736640566837)
                  ·
                    refine ⟨54033906115934881560053141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 576361665236638736640566837 54033906115934881560053141)
                    ·
                      refine ⟨2532839349184447573127491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54033906115934881560053141 2532839349184447573127491)
                      ·
                        rfl

theorem cell23_4932687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_4932687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932687 prefixEnd_4932687 := by exact prefixLift 4932687
  have htrace : WordTrace (prefixWord ++ tailWord_4932687) baseStart_4932687 baseEnd_4932687 := by
    simpa [prefixWord, tailWord_4932687, baseEnd_4932687] using wordTrace_append hprefix tailTrace_4932687
  have hstable : (prefixWord ++ tailWord_4932687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932687).length < 2 ^ (prefixWord ++ tailWord_4932687).sum := by decide
  have hdescent : baseEnd_4932687 < baseStart_4932687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932702 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4932702 : Nat := 118140960795 + 4932702 * 2 ^ 59
def prefixEnd_4932702 : Nat := 4983230072969 + 3 ^ 40 * 4932702 * 2
def baseEnd_4932702 : Nat := 2532847051394265014439923

theorem tailTrace_4932702 : CollatzResearch.WordTrace tailWord_4932702 prefixEnd_4932702 2532847051394265014439923 := by
  unfold tailWord_4932702
  simp only [CollatzResearch.WordTrace]
  refine ⟨22488802771958820909595045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119940281450447044851173573 22488802771958820909595045)
  ·
    refine ⟨4216650519742278920549071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22488802771958820909595045 4216650519742278920549071)
    ·
      refine ⟨6324975779613418380823607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216650519742278920549071 6324975779613418380823607)
      ·
        refine ⟨9487463669420127571235411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324975779613418380823607 9487463669420127571235411)
        ·
          refine ⟨14231195504130191356853117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487463669420127571235411 14231195504130191356853117)
          ·
            refine ⟨5336698314048821758819919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14231195504130191356853117 5336698314048821758819919)
            ·
              refine ⟨8005047471073232638229879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5336698314048821758819919 8005047471073232638229879)
              ·
                refine ⟨12007571206609848957344819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8005047471073232638229879 12007571206609848957344819)
                ·
                  refine ⟨18011356809914773436017229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12007571206609848957344819 18011356809914773436017229)
                  ·
                    refine ⟨6754258803718040038506461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18011356809914773436017229 6754258803718040038506461)
                    ·
                      refine ⟨2532847051394265014439923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754258803718040038506461 2532847051394265014439923)
                      ·
                        rfl

theorem cell23_4932702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4932702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932702 prefixEnd_4932702 := by exact prefixLift 4932702
  have htrace : WordTrace (prefixWord ++ tailWord_4932702) baseStart_4932702 baseEnd_4932702 := by
    simpa [prefixWord, tailWord_4932702, baseEnd_4932702] using wordTrace_append hprefix tailTrace_4932702
  have hstable : (prefixWord ++ tailWord_4932702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932702).length < 2 ^ (prefixWord ++ tailWord_4932702).sum := by decide
  have hdescent : baseEnd_4932702 < baseStart_4932702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932704 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_4932704 : Nat := 118140960795 + 4932704 * 2 ^ 59
def prefixEnd_4932704 : Nat := 4983230072969 + 3 ^ 40 * 4932704 * 2
def baseEnd_4932704 : Nat := 2532848078355574006614913

theorem tailTrace_4932704 : CollatzResearch.WordTrace tailWord_4932704 prefixEnd_4932704 2532848078355574006614913 := by
  unfold tailWord_4932704
  simp only [CollatzResearch.WordTrace]
  refine ⟨89955247560831660809166583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119940330081108881078888777 89955247560831660809166583)
  ·
    refine ⟨134932871341247491213749875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89955247560831660809166583 134932871341247491213749875)
    ·
      refine ⟨202399307011871236820624813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134932871341247491213749875 202399307011871236820624813)
      ·
        refine ⟨75899740129451713807734305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202399307011871236820624813 75899740129451713807734305)
        ·
          refine ⟨56924805097088785355800729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75899740129451713807734305 56924805097088785355800729)
          ·
            refine ⟨42693603822816589016850547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56924805097088785355800729 42693603822816589016850547)
            ·
              refine ⟨64040405734224883525275821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42693603822816589016850547 64040405734224883525275821)
              ·
                refine ⟨24015152150334331321978433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64040405734224883525275821 24015152150334331321978433)
                ·
                  refine ⟨18011364112750748491483825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24015152150334331321978433 18011364112750748491483825)
                  ·
                    refine ⟨13508523084563061368612869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18011364112750748491483825 13508523084563061368612869)
                    ·
                      refine ⟨2532848078355574006614913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13508523084563061368612869 2532848078355574006614913)
                      ·
                        rfl

theorem cell23_4932704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_4932704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932704 prefixEnd_4932704 := by exact prefixLift 4932704
  have htrace : WordTrace (prefixWord ++ tailWord_4932704) baseStart_4932704 baseEnd_4932704 := by
    simpa [prefixWord, tailWord_4932704, baseEnd_4932704] using wordTrace_append hprefix tailTrace_4932704
  have hstable : (prefixWord ++ tailWord_4932704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932704).length < 2 ^ (prefixWord ++ tailWord_4932704).sum := by decide
  have hdescent : baseEnd_4932704 < baseStart_4932704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932712 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4932712 : Nat := 118140960795 + 4932712 * 2 ^ 59
def prefixEnd_4932712 : Nat := 4983230072969 + 3 ^ 40 * 4932712 * 2
def baseEnd_4932712 : Nat := 2532852186200809975314877

theorem tailTrace_4932712 : CollatzResearch.WordTrace tailWord_4932712 prefixEnd_4932712 2532852186200809975314877 := by
  unfold tailWord_4932712
  simp only [CollatzResearch.WordTrace]
  refine ⟨89955393452817169492312195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119940524603756225989749593 89955393452817169492312195)
  ·
    refine ⟨134933090179225754238468293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89955393452817169492312195 134933090179225754238468293)
    ·
      refine ⟨25299954408604828919712805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134933090179225754238468293 25299954408604828919712805)
      ·
        refine ⟨4743741451613405422446151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25299954408604828919712805 4743741451613405422446151)
        ·
          refine ⟨7115612177420108133669227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743741451613405422446151 7115612177420108133669227)
          ·
            refine ⟨10673418266130162200503841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7115612177420108133669227 10673418266130162200503841)
            ·
              refine ⟨8005063699597621650377881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10673418266130162200503841 8005063699597621650377881)
              ·
                refine ⟨6003797774698216237783411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8005063699597621650377881 6003797774698216237783411)
                ·
                  refine ⟨9005696662047324356675117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6003797774698216237783411 9005696662047324356675117)
                  ·
                    refine ⟨3377136248267746633753169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9005696662047324356675117 3377136248267746633753169)
                    ·
                      refine ⟨2532852186200809975314877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377136248267746633753169 2532852186200809975314877)
                      ·
                        rfl

theorem cell23_4932712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4932712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932712 prefixEnd_4932712 := by exact prefixLift 4932712
  have htrace : WordTrace (prefixWord ++ tailWord_4932712) baseStart_4932712 baseEnd_4932712 := by
    simpa [prefixWord, tailWord_4932712, baseEnd_4932712] using wordTrace_append hprefix tailTrace_4932712
  have hstable : (prefixWord ++ tailWord_4932712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932712).length < 2 ^ (prefixWord ++ tailWord_4932712).sum := by decide
  have hdescent : baseEnd_4932712 < baseStart_4932712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932778 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4932778 : Nat := 118140960795 + 4932778 * 2 ^ 59
def prefixEnd_4932778 : Nat := 4983230072969 + 3 ^ 40 * 4932778 * 2
def baseEnd_4932778 : Nat := 844295358641335572363191

theorem tailTrace_4932778 : CollatzResearch.WordTrace tailWord_4932778 prefixEnd_4932778 844295358641335572363191 := by
  unfold tailWord_4932778
  simp only [CollatzResearch.WordTrace]
  refine ⟨44978298530848808064131747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119942129415596821504351325 44978298530848808064131747)
  ·
    refine ⟨67467447796273212096197621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44978298530848808064131747 67467447796273212096197621)
    ·
      refine ⟨6325073230900613634018527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67467447796273212096197621 6325073230900613634018527)
      ·
        refine ⟨9487609846350920451027791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325073230900613634018527 9487609846350920451027791)
        ·
          refine ⟨14231414769526380676541687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487609846350920451027791 14231414769526380676541687)
          ·
            refine ⟨21347122154289571014812531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14231414769526380676541687 21347122154289571014812531)
            ·
              refine ⟨32020683231434356522218797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21347122154289571014812531 32020683231434356522218797)
              ·
                refine ⟨12007756211787883695832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32020683231434356522218797 12007756211787883695832049)
                ·
                  refine ⟨9005817158840912771874037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12007756211787883695832049 9005817158840912771874037)
                  ·
                    refine ⟨844295358641335572363191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9005817158840912771874037 844295358641335572363191)
                    ·
                      rfl

theorem cell23_4932778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4932778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932778 prefixEnd_4932778 := by exact prefixLift 4932778
  have htrace : WordTrace (prefixWord ++ tailWord_4932778) baseStart_4932778 baseEnd_4932778 := by
    simpa [prefixWord, tailWord_4932778, baseEnd_4932778] using wordTrace_append hprefix tailTrace_4932778
  have hstable : (prefixWord ++ tailWord_4932778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932778).length < 2 ^ (prefixWord ++ tailWord_4932778).sum := by decide
  have hdescent : baseEnd_4932778 < baseStart_4932778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932794 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_4932794 : Nat := 118140960795 + 4932794 * 2 ^ 59
def prefixEnd_4932794 : Nat := 4983230072969 + 3 ^ 40 * 4932794 * 2
def baseEnd_4932794 : Nat := 2532894291614478654489499

theorem tailTrace_4932794 : CollatzResearch.WordTrace tailWord_4932794 prefixEnd_4932794 2532894291614478654489499 := by
  unfold tailWord_4932794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44978444422834316747277359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119942518460891511326072957 44978444422834316747277359)
  ·
    refine ⟨67467666634251475120916039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44978444422834316747277359 67467666634251475120916039)
    ·
      refine ⟨101201499951377212681374059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67467666634251475120916039 101201499951377212681374059)
      ·
        refine ⟨151802249927065819022061089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101201499951377212681374059 151802249927065819022061089)
        ·
          refine ⟨113851687445299364266545817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151802249927065819022061089 113851687445299364266545817)
          ·
            refine ⟨85388765583974523199909363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113851687445299364266545817 85388765583974523199909363)
            ·
              refine ⟨128083148375961784799864045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85388765583974523199909363 128083148375961784799864045)
              ·
                refine ⟨48031180640985669299949017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128083148375961784799864045 48031180640985669299949017)
                ·
                  refine ⟨36023385480739251974961763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48031180640985669299949017 36023385480739251974961763)
                  ·
                    refine ⟨54035078221108877962442645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36023385480739251974961763 54035078221108877962442645)
                    ·
                      refine ⟨2532894291614478654489499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54035078221108877962442645 2532894291614478654489499)
                      ·
                        rfl

theorem cell23_4932794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_4932794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932794 prefixEnd_4932794 := by exact prefixLift 4932794
  have htrace : WordTrace (prefixWord ++ tailWord_4932794) baseStart_4932794 baseEnd_4932794 := by
    simpa [prefixWord, tailWord_4932794, baseEnd_4932794] using wordTrace_append hprefix tailTrace_4932794
  have hstable : (prefixWord ++ tailWord_4932794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932794).length < 2 ^ (prefixWord ++ tailWord_4932794).sum := by decide
  have hdescent : baseEnd_4932794 < baseStart_4932794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932798 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4932798 : Nat := 118140960795 + 4932798 * 2 ^ 59
def prefixEnd_4932798 : Nat := 4983230072969 + 3 ^ 40 * 4932798 * 2
def baseEnd_4932798 : Nat := 2532896345537096638839481

theorem tailTrace_4932798 : CollatzResearch.WordTrace tailWord_4932798 prefixEnd_4932798 2532896345537096638839481 := by
  unfold tailWord_4932798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22489240447915346959031881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119942615722215183781503365 22489240447915346959031881)
  ·
    refine ⟨16866930335936510219273911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22489240447915346959031881 16866930335936510219273911)
    ·
      refine ⟨25300395503904765328910867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16866930335936510219273911 25300395503904765328910867)
      ·
        refine ⟨37950593255857147993366301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25300395503904765328910867 37950593255857147993366301)
        ·
          refine ⟨14231472470946430497512363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37950593255857147993366301 14231472470946430497512363)
          ·
            refine ⟨21347208706419645746268545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14231472470946430497512363 21347208706419645746268545)
            ·
              refine ⟨16010406529814734309701409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21347208706419645746268545 16010406529814734309701409)
              ·
                refine ⟨12007804897361050732276057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16010406529814734309701409 12007804897361050732276057)
                ·
                  refine ⟨9005853673020788049207043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12007804897361050732276057 9005853673020788049207043)
                  ·
                    refine ⟨13508780509531182073810565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9005853673020788049207043 13508780509531182073810565)
                    ·
                      refine ⟨2532896345537096638839481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13508780509531182073810565 2532896345537096638839481)
                      ·
                        rfl

theorem cell23_4932798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4932798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932798 prefixEnd_4932798 := by exact prefixLift 4932798
  have htrace : WordTrace (prefixWord ++ tailWord_4932798) baseStart_4932798 baseEnd_4932798 := by
    simpa [prefixWord, tailWord_4932798, baseEnd_4932798] using wordTrace_append hprefix tailTrace_4932798
  have hstable : (prefixWord ++ tailWord_4932798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932798).length < 2 ^ (prefixWord ++ tailWord_4932798).sum := by decide
  have hdescent : baseEnd_4932798 < baseStart_4932798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932858 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_4932858 : Nat := 118140960795 + 4932858 * 2 ^ 59
def prefixEnd_4932858 : Nat := 4983230072969 + 3 ^ 40 * 4932858 * 2
def baseEnd_4932858 : Nat := 2532927154376366404089205

theorem tailTrace_4932858 : CollatzResearch.WordTrace tailWord_4932858 prefixEnd_4932858 2532927154376366404089205 := by
  unfold tailWord_4932858
  simp only [CollatzResearch.WordTrace]
  refine ⟨44979027990776351479859807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119944074642070270612959485 44979027990776351479859807)
  ·
    refine ⟨67468541986164527219789711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44979027990776351479859807 67468541986164527219789711)
    ·
      refine ⟨101202812979246790829684567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67468541986164527219789711 101202812979246790829684567)
      ·
        refine ⟨151804219468870186244526851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101202812979246790829684567 151804219468870186244526851)
        ·
          refine ⟨227706329203305279366790277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151804219468870186244526851 227706329203305279366790277)
          ·
            refine ⟨42694936725619739881273177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227706329203305279366790277 42694936725619739881273177)
            ·
              refine ⟨32021202544214804910954883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42694936725619739881273177 32021202544214804910954883)
              ·
                refine ⟨48031803816322207366432325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32021202544214804910954883 48031803816322207366432325)
                ·
                  refine ⟨9005963215560413881206061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48031803816322207366432325 9005963215560413881206061)
                  ·
                    refine ⟨3377236205835155205452273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9005963215560413881206061 3377236205835155205452273)
                    ·
                      refine ⟨2532927154376366404089205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377236205835155205452273 2532927154376366404089205)
                      ·
                        rfl

theorem cell23_4932858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_4932858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932858 prefixEnd_4932858 := by exact prefixLift 4932858
  have htrace : WordTrace (prefixWord ++ tailWord_4932858) baseStart_4932858 baseEnd_4932858 := by
    simpa [prefixWord, tailWord_4932858, baseEnd_4932858] using wordTrace_append hprefix tailTrace_4932858
  have hstable : (prefixWord ++ tailWord_4932858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932858).length < 2 ^ (prefixWord ++ tailWord_4932858).sum := by decide
  have hdescent : baseEnd_4932858 < baseStart_4932858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932865 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4932865 : Nat := 118140960795 + 4932865 * 2 ^ 59
def prefixEnd_4932865 : Nat := 4983230072969 + 3 ^ 40 * 4932865 * 2
def baseEnd_4932865 : Nat := 2532930748740947876701673

theorem tailTrace_4932865 : CollatzResearch.WordTrace tailWord_4932865 prefixEnd_4932865 2532930748740947876701673 := by
  unfold tailWord_4932865
  simp only [CollatzResearch.WordTrace]
  refine ⟨179916367274080046114944049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119944244849386697409962699 179916367274080046114944049)
  ·
    refine ⟨134937275455560034586208037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179916367274080046114944049 134937275455560034586208037)
    ·
      refine ⟨25300739147917506484914007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134937275455560034586208037 25300739147917506484914007)
      ·
        refine ⟨37951108721876259727371011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25300739147917506484914007 37951108721876259727371011)
        ·
          refine ⟨56926663082814389591056517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37951108721876259727371011 56926663082814389591056517)
          ·
            refine ⟨10673749328027698048323097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56926663082814389591056517 10673749328027698048323097)
            ·
              refine ⟨8005311996020773536242323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10673749328027698048323097 8005311996020773536242323)
              ·
                refine ⟨12007967994031160304363485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8005311996020773536242323 12007967994031160304363485)
                ·
                  refine ⟨4502987997761685114136307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12007967994031160304363485 4502987997761685114136307)
                  ·
                    refine ⟨6754481996642527671204461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4502987997761685114136307 6754481996642527671204461)
                    ·
                      refine ⟨2532930748740947876701673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754481996642527671204461 2532930748740947876701673)
                      ·
                        rfl

theorem cell23_4932865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4932865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932865 prefixEnd_4932865 := by exact prefixLift 4932865
  have htrace : WordTrace (prefixWord ++ tailWord_4932865) baseStart_4932865 baseEnd_4932865 := by
    simpa [prefixWord, tailWord_4932865, baseEnd_4932865] using wordTrace_append hprefix tailTrace_4932865
  have hstable : (prefixWord ++ tailWord_4932865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932865).length < 2 ^ (prefixWord ++ tailWord_4932865).sum := by decide
  have hdescent : baseEnd_4932865 < baseStart_4932865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932888 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_4932888 : Nat := 118140960795 + 4932888 * 2 ^ 59
def prefixEnd_4932888 : Nat := 4983230072969 + 3 ^ 40 * 4932888 * 2
def baseEnd_4932888 : Nat := 2532942558796001286714067

theorem tailTrace_4932888 : CollatzResearch.WordTrace tailWord_4932888 prefixEnd_4932888 2532942558796001286714067 := by
  unfold tailWord_4932888
  simp only [CollatzResearch.WordTrace]
  refine ⟨89958603076498360521515659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119944804101997814028687545 89958603076498360521515659)
  ·
    refine ⟨134937904614747540782273489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89958603076498360521515659 134937904614747540782273489)
    ·
      refine ⟨101203428461060655586705117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134937904614747540782273489 101203428461060655586705117)
      ·
        refine ⟨37951285672897745845014419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101203428461060655586705117 37951285672897745845014419)
        ·
          refine ⟨56926928509346618767521629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37951285672897745845014419 56926928509346618767521629)
          ·
            refine ⟨21347598191004982037820611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56926928509346618767521629 21347598191004982037820611)
            ·
              refine ⟨32021397286507473056730917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21347598191004982037820611 32021397286507473056730917)
              ·
                refine ⟨6004011991220151198137047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32021397286507473056730917 6004011991220151198137047)
                ·
                  refine ⟨9006017986830226797205571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6004011991220151198137047 9006017986830226797205571)
                  ·
                    refine ⟨13509026980245340195808357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9006017986830226797205571 13509026980245340195808357)
                    ·
                      refine ⟨2532942558796001286714067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13509026980245340195808357 2532942558796001286714067)
                      ·
                        rfl

theorem cell23_4932888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_4932888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932888 prefixEnd_4932888 := by exact prefixLift 4932888
  have htrace : WordTrace (prefixWord ++ tailWord_4932888) baseStart_4932888 baseEnd_4932888 := by
    simpa [prefixWord, tailWord_4932888, baseEnd_4932888] using wordTrace_append hprefix tailTrace_4932888
  have hstable : (prefixWord ++ tailWord_4932888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932888).length < 2 ^ (prefixWord ++ tailWord_4932888).sum := by decide
  have hdescent : baseEnd_4932888 < baseStart_4932888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932932 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4932932 : Nat := 118140960795 + 4932932 * 2 ^ 59
def prefixEnd_4932932 : Nat := 4983230072969 + 3 ^ 40 * 4932932 * 2
def baseEnd_4932932 : Nat := 844321717314933038187955

theorem tailTrace_4932932 : CollatzResearch.WordTrace tailWord_4932932 prefixEnd_4932932 844321717314933038187955 := by
  unfold tailWord_4932932
  simp only [CollatzResearch.WordTrace]
  refine ⟨89959405482418658278816525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119945873976558211038422033 89959405482418658278816525)
  ·
    refine ⟨33734777055906996854556197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89959405482418658278816525 33734777055906996854556197)
    ·
      refine ⟨6325270697982561910229287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33734777055906996854556197 6325270697982561910229287)
      ·
        refine ⟨9487906046973842865343931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325270697982561910229287 9487906046973842865343931)
        ·
          refine ⟨14231859070460764298015897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9487906046973842865343931 14231859070460764298015897)
          ·
            refine ⟨10673894302845573223511923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14231859070460764298015897 10673894302845573223511923)
            ·
              refine ⟨16010841454268359835267885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10673894302845573223511923 16010841454268359835267885)
              ·
                refine ⟨6004065545350634938225457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16010841454268359835267885 6004065545350634938225457)
                ·
                  refine ⟨4503049159012976203669093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004065545350634938225457 4503049159012976203669093)
                  ·
                    refine ⟨844321717314933038187955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503049159012976203669093 844321717314933038187955)
                    ·
                      rfl

theorem cell23_4932932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4932932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932932 prefixEnd_4932932 := by exact prefixLift 4932932
  have htrace : WordTrace (prefixWord ++ tailWord_4932932) baseStart_4932932 baseEnd_4932932 := by
    simpa [prefixWord, tailWord_4932932, baseEnd_4932932] using wordTrace_append hprefix tailTrace_4932932
  have hstable : (prefixWord ++ tailWord_4932932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932932).length < 2 ^ (prefixWord ++ tailWord_4932932).sum := by decide
  have hdescent : baseEnd_4932932 < baseStart_4932932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932961 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_4932961 : Nat := 118140960795 + 4932961 * 2 ^ 59
def prefixEnd_4932961 : Nat := 4983230072969 + 3 ^ 40 * 4932961 * 2
def baseEnd_4932961 : Nat := 2532980042883779501101231

theorem tailTrace_4932961 : CollatzResearch.WordTrace tailWord_4932961 prefixEnd_4932961 2532980042883779501101231 := by
  unfold tailWord_4932961
  simp only [CollatzResearch.WordTrace]
  refine ⟨179919868681732254510438737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119946579121154836340292491 179919868681732254510438737)
  ·
    refine ⟨134939901511299190882829053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179919868681732254510438737 134939901511299190882829053)
    ·
      refine ⟨50602463066737196581060895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134939901511299190882829053 50602463066737196581060895)
      ·
        refine ⟨75903694600105794871591343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50602463066737196581060895 75903694600105794871591343)
        ·
          refine ⟨113855541900158692307387015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75903694600105794871591343 113855541900158692307387015)
          ·
            refine ⟨170783312850238038461080523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113855541900158692307387015 170783312850238038461080523)
            ·
              refine ⟨256174969275357057691620785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170783312850238038461080523 256174969275357057691620785)
              ·
                refine ⟨192131226956517793268715589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256174969275357057691620785 192131226956517793268715589)
                ·
                  refine ⟨36024605054347086237884173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192131226956517793268715589 36024605054347086237884173)
                  ·
                    refine ⟨13509226895380157339206565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36024605054347086237884173 13509226895380157339206565)
                    ·
                      refine ⟨2532980042883779501101231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13509226895380157339206565 2532980042883779501101231)
                      ·
                        rfl

theorem cell23_4932961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_4932961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932961 prefixEnd_4932961 := by exact prefixLift 4932961
  have htrace : WordTrace (prefixWord ++ tailWord_4932961) baseStart_4932961 baseEnd_4932961 := by
    simpa [prefixWord, tailWord_4932961, baseEnd_4932961] using wordTrace_append hprefix tailTrace_4932961
  have hstable : (prefixWord ++ tailWord_4932961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932961).length < 2 ^ (prefixWord ++ tailWord_4932961).sum := by decide
  have hdescent : baseEnd_4932961 < baseStart_4932961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932972 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_4932972 : Nat := 118140960795 + 4932972 * 2 ^ 59
def prefixEnd_4932972 : Nat := 4983230072969 + 3 ^ 40 * 4932972 * 2
def baseEnd_4932972 : Nat := 2532985691170978958063681

theorem tailTrace_4932972 : CollatzResearch.WordTrace tailWord_4932972 prefixEnd_4932972 2532985691170978958063681 := by
  unfold tailWord_4932972
  simp only [CollatzResearch.WordTrace]
  refine ⟨89960134942346201694544585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119946846589794935592726113 89960134942346201694544585)
  ·
    refine ⟨67470101206759651270908439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89960134942346201694544585 67470101206759651270908439)
    ·
      refine ⟨101205151810139476906362659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67470101206759651270908439 101205151810139476906362659)
      ·
        refine ⟨151807727715209215359543989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101205151810139476906362659 151807727715209215359543989)
        ·
          refine ⟨14231974473300863939957249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151807727715209215359543989 14231974473300863939957249)
          ·
            refine ⟨10673980854975647954967937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14231974473300863939957249 10673980854975647954967937)
            ·
              refine ⟨8005485641231735966225953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10673980854975647954967937 8005485641231735966225953)
              ·
                refine ⟨6004114230923801974669465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8005485641231735966225953 6004114230923801974669465)
                ·
                  refine ⟨4503085673192851481002099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004114230923801974669465 4503085673192851481002099)
                  ·
                    refine ⟨6754628509789277221503149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503085673192851481002099 6754628509789277221503149)
                    ·
                      refine ⟨2532985691170978958063681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754628509789277221503149 2532985691170978958063681)
                      ·
                        rfl

theorem cell23_4932972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_4932972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932972 prefixEnd_4932972 := by exact prefixLift 4932972
  have htrace : WordTrace (prefixWord ++ tailWord_4932972) baseStart_4932972 baseEnd_4932972 := by
    simpa [prefixWord, tailWord_4932972, baseEnd_4932972] using wordTrace_append hprefix tailTrace_4932972
  have hstable : (prefixWord ++ tailWord_4932972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932972).length < 2 ^ (prefixWord ++ tailWord_4932972).sum := by decide
  have hdescent : baseEnd_4932972 < baseStart_4932972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4932995 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 1, 4, 2]
def baseStart_4932995 : Nat := 118140960795 + 4932995 * 2 ^ 59
def prefixEnd_4932995 : Nat := 4983230072969 + 3 ^ 40 * 4932995 * 2
def baseEnd_4932995 : Nat := 2532997501226032368076075

theorem tailTrace_4932995 : CollatzResearch.WordTrace tailWord_4932995 prefixEnd_4932995 2532997501226032368076075 := by
  unfold tailWord_4932995
  simp only [CollatzResearch.WordTrace]
  refine ⟨179921108763609078317176439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119947405842406052211450959 179921108763609078317176439)
  ·
    refine ⟨269881663145413617475764659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179921108763609078317176439 269881663145413617475764659)
    ·
      refine ⟨404822494718120426213646989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269881663145413617475764659 404822494718120426213646989)
      ·
        refine ⟨151808435519295159830117621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404822494718120426213646989 151808435519295159830117621)
        ·
          refine ⟨14232040829933921234073527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151808435519295159830117621 14232040829933921234073527)
          ·
            refine ⟨21348061244900881851110291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232040829933921234073527 21348061244900881851110291)
            ·
              refine ⟨32022091867351322776665437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21348061244900881851110291 32022091867351322776665437)
              ·
                refine ⟨12008284450256746041249539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32022091867351322776665437 12008284450256746041249539)
                ·
                  refine ⟨18012426675385119061874309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12008284450256746041249539 18012426675385119061874309)
                  ·
                    refine ⟨3377330001634709824101433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18012426675385119061874309 3377330001634709824101433)
                    ·
                      refine ⟨2532997501226032368076075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377330001634709824101433 2532997501226032368076075)
                      ·
                        rfl

theorem cell23_4932995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_4932995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4932995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4932995 prefixEnd_4932995 := by exact prefixLift 4932995
  have htrace : WordTrace (prefixWord ++ tailWord_4932995) baseStart_4932995 baseEnd_4932995 := by
    simpa [prefixWord, tailWord_4932995, baseEnd_4932995] using wordTrace_append hprefix tailTrace_4932995
  have hstable : (prefixWord ++ tailWord_4932995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4932995).length < 2 ^ (prefixWord ++ tailWord_4932995).sum := by decide
  have hdescent : baseEnd_4932995 < baseStart_4932995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4932995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933012 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4933012 : Nat := 118140960795 + 4933012 * 2 ^ 59
def prefixEnd_4933012 : Nat := 4983230072969 + 3 ^ 40 * 4933012 * 2
def baseEnd_4933012 : Nat := 2533006230397158801563497

theorem tailTrace_4933012 : CollatzResearch.WordTrace tailWord_4933012 prefixEnd_4933012 2533006230397158801563497 := by
  unfold tailWord_4933012
  simp only [CollatzResearch.WordTrace]
  refine ⟨89960864402273745110272645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119947819203031660147030193 89960864402273745110272645)
  ·
    refine ⟨16867662075426327208176121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89960864402273745110272645 16867662075426327208176121)
    ·
      refine ⟨12650746556569745406132091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16867662075426327208176121 12650746556569745406132091)
      ·
        refine ⟨18976119834854618109198137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12650746556569745406132091 18976119834854618109198137)
        ·
          refine ⟨14232089876140963581898603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18976119834854618109198137 14232089876140963581898603)
          ·
            refine ⟨21348134814211445372847905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232089876140963581898603 21348134814211445372847905)
            ·
              refine ⟨16011101110658584029635929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21348134814211445372847905 16011101110658584029635929)
              ·
                refine ⟨12008325832993938022226947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16011101110658584029635929 12008325832993938022226947)
                ·
                  refine ⟨18012488749490907033340421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12008325832993938022226947 18012488749490907033340421)
                  ·
                    refine ⟨3377341640529545068751329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18012488749490907033340421 3377341640529545068751329)
                    ·
                      refine ⟨2533006230397158801563497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377341640529545068751329 2533006230397158801563497)
                      ·
                        rfl

theorem cell23_4933012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4933012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933012 prefixEnd_4933012 := by exact prefixLift 4933012
  have htrace : WordTrace (prefixWord ++ tailWord_4933012) baseStart_4933012 baseEnd_4933012 := by
    simpa [prefixWord, tailWord_4933012, baseEnd_4933012] using wordTrace_append hprefix tailTrace_4933012
  have hstable : (prefixWord ++ tailWord_4933012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933012).length < 2 ^ (prefixWord ++ tailWord_4933012).sum := by decide
  have hdescent : baseEnd_4933012 < baseStart_4933012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933016 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4933016 : Nat := 118140960795 + 4933016 * 2 ^ 59
def prefixEnd_4933016 : Nat := 4983230072969 + 3 ^ 40 * 4933016 * 2
def baseEnd_4933016 : Nat := 2533008284319776785913479

theorem tailTrace_4933016 : CollatzResearch.WordTrace tailWord_4933016 prefixEnd_4933016 2533008284319776785913479 := by
  unfold tailWord_4933016
  simp only [CollatzResearch.WordTrace]
  refine ⟨89960937348266499451845451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119947916464355332602460601 89960937348266499451845451)
  ·
    refine ⟨134941406022399749177768177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89960937348266499451845451 134941406022399749177768177)
    ·
      refine ⟨101206054516799811883326133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134941406022399749177768177 101206054516799811883326133)
      ·
        refine ⟨9488067610949982364061825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101206054516799811883326133 9488067610949982364061825)
        ·
          refine ⟨7116050708212486773046369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9488067610949982364061825 7116050708212486773046369)
          ·
            refine ⟨5337038031159365079784777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7116050708212486773046369 5337038031159365079784777)
            ·
              refine ⟨4002778523369523809838583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5337038031159365079784777 4002778523369523809838583)
              ·
                refine ⟨6004167785054285714757875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002778523369523809838583 6004167785054285714757875)
                ·
                  refine ⟨9006251677581428572136813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6004167785054285714757875 9006251677581428572136813)
                  ·
                    refine ⟨3377344379093035714551305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9006251677581428572136813 3377344379093035714551305)
                    ·
                      refine ⟨2533008284319776785913479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377344379093035714551305 2533008284319776785913479)
                      ·
                        rfl

theorem cell23_4933016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4933016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933016 prefixEnd_4933016 := by exact prefixLift 4933016
  have htrace : WordTrace (prefixWord ++ tailWord_4933016) baseStart_4933016 baseEnd_4933016 := by
    simpa [prefixWord, tailWord_4933016, baseEnd_4933016] using wordTrace_append hprefix tailTrace_4933016
  have hstable : (prefixWord ++ tailWord_4933016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933016).length < 2 ^ (prefixWord ++ tailWord_4933016).sum := by decide
  have hdescent : baseEnd_4933016 < baseStart_4933016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933045 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4933045 : Nat := 118140960795 + 4933045 * 2 ^ 59
def prefixEnd_4933045 : Nat := 4983230072969 + 3 ^ 40 * 4933045 * 2
def baseEnd_4933045 : Nat := 2533023175258757172450845

theorem tailTrace_4933045 : CollatzResearch.WordTrace tailWord_4933045 prefixEnd_4933045 2533023175258757172450845 := by
  unfold tailWord_4933045
  simp only [CollatzResearch.WordTrace]
  refine ⟨179922932413427936856496589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119948621608951957904331059 179922932413427936856496589)
  ·
    refine ⟨67471099655035476321186221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179922932413427936856496589 67471099655035476321186221)
    ·
      refine ⟨25301662370638303620444833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67471099655035476321186221 25301662370638303620444833)
      ·
        refine ⟨18976246777978727715333625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25301662370638303620444833 18976246777978727715333625)
        ·
          refine ⟨14232185083484045786500219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18976246777978727715333625 14232185083484045786500219)
          ·
            refine ⟨21348277625226068679750329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14232185083484045786500219 21348277625226068679750329)
            ·
              refine ⟨16011208218919551509812747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21348277625226068679750329 16011208218919551509812747)
              ·
                refine ⟨24016812328379327264719121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16011208218919551509812747 24016812328379327264719121)
                ·
                  refine ⟨18012609246284495448539341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24016812328379327264719121 18012609246284495448539341)
                  ·
                    refine ⟨6754728467356685793202253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18012609246284495448539341 6754728467356685793202253)
                    ·
                      refine ⟨2533023175258757172450845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754728467356685793202253 2533023175258757172450845)
                      ·
                        rfl

theorem cell23_4933045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4933045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933045 prefixEnd_4933045 := by exact prefixLift 4933045
  have htrace : WordTrace (prefixWord ++ tailWord_4933045) baseStart_4933045 baseEnd_4933045 := by
    simpa [prefixWord, tailWord_4933045, baseEnd_4933045] using wordTrace_append hprefix tailTrace_4933045
  have hstable : (prefixWord ++ tailWord_4933045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933045).length < 2 ^ (prefixWord ++ tailWord_4933045).sum := by decide
  have hdescent : baseEnd_4933045 < baseStart_4933045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933085 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4933085 : Nat := 118140960795 + 4933085 * 2 ^ 59
def prefixEnd_4933085 : Nat := 4983230072969 + 3 ^ 40 * 4933085 * 2
def baseEnd_4933085 : Nat := 2533043714484937015950661

theorem tailTrace_4933085 : CollatzResearch.WordTrace tailWord_4933085 prefixEnd_4933085 2533043714484937015950661 := by
  unfold tailWord_4933085
  simp only [CollatzResearch.WordTrace]
  refine ⟨179924391333283023687952709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119949594222188682458635139 179924391333283023687952709)
  ·
    refine ⟨33735823374990566941491133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179924391333283023687952709 33735823374990566941491133)
    ·
      refine ⟨12650933765621462603059175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33735823374990566941491133 12650933765621462603059175)
      ·
        refine ⟨18976400648432193904588763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12650933765621462603059175 18976400648432193904588763)
        ·
          refine ⟨28464600972648290856883145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18976400648432193904588763 28464600972648290856883145)
          ·
            refine ⟨21348450729486218142662359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28464600972648290856883145 21348450729486218142662359)
            ·
              refine ⟨32022676094229327213993539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21348450729486218142662359 32022676094229327213993539)
              ·
                refine ⟨48034014141343990820990309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32022676094229327213993539 48034014141343990820990309)
                ·
                  refine ⟨9006377651501998278935683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48034014141343990820990309 9006377651501998278935683)
                  ·
                    refine ⟨13509566477252997418403525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9006377651501998278935683 13509566477252997418403525)
                    ·
                      refine ⟨2533043714484937015950661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13509566477252997418403525 2533043714484937015950661)
                      ·
                        rfl

theorem cell23_4933085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4933085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933085 prefixEnd_4933085 := by exact prefixLift 4933085
  have htrace : WordTrace (prefixWord ++ tailWord_4933085) baseStart_4933085 baseEnd_4933085 := by
    simpa [prefixWord, tailWord_4933085, baseEnd_4933085] using wordTrace_append hprefix tailTrace_4933085
  have hstable : (prefixWord ++ tailWord_4933085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933085).length < 2 ^ (prefixWord ++ tailWord_4933085).sum := by decide
  have hdescent : baseEnd_4933085 < baseStart_4933085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933088 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_4933088 : Nat := 118140960795 + 4933088 * 2 ^ 59
def prefixEnd_4933088 : Nat := 4983230072969 + 3 ^ 40 * 4933088 * 2
def baseEnd_4933088 : Nat := 2533045254926900504213147

theorem tailTrace_4933088 : CollatzResearch.WordTrace tailWord_4933088 prefixEnd_4933088 2533045254926900504213147 := by
  unfold tailWord_4933088
  simp only [CollatzResearch.WordTrace]
  refine ⟨89962250376136077600155959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119949667168181436800207945 89962250376136077600155959)
  ·
    refine ⟨134943375564204116400233939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89962250376136077600155959 134943375564204116400233939)
    ·
      refine ⟨202415063346306174600350909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134943375564204116400233939 202415063346306174600350909)
      ·
        refine ⟨75905648754864815475131591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202415063346306174600350909 75905648754864815475131591)
        ·
          refine ⟨113858473132297223212697387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75905648754864815475131591 113858473132297223212697387)
          ·
            refine ⟨170787709698445834819046081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113858473132297223212697387 170787709698445834819046081)
            ·
              refine ⟨128090782273834376114284561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170787709698445834819046081 128090782273834376114284561)
              ·
                refine ⟨96068086705375782085713421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128090782273834376114284561 96068086705375782085713421)
                ·
                  refine ⟨36025532514515918282142533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96068086705375782085713421 36025532514515918282142533)
                  ·
                    refine ⟨6754787346471734677901725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36025532514515918282142533 6754787346471734677901725)
                    ·
                      refine ⟨2533045254926900504213147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6754787346471734677901725 2533045254926900504213147)
                      ·
                        rfl

theorem cell23_4933088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_4933088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933088 prefixEnd_4933088 := by exact prefixLift 4933088
  have htrace : WordTrace (prefixWord ++ tailWord_4933088) baseStart_4933088 baseEnd_4933088 := by
    simpa [prefixWord, tailWord_4933088, baseEnd_4933088] using wordTrace_append hprefix tailTrace_4933088
  have hstable : (prefixWord ++ tailWord_4933088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933088).length < 2 ^ (prefixWord ++ tailWord_4933088).sum := by decide
  have hdescent : baseEnd_4933088 < baseStart_4933088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933162 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4933162 : Nat := 118140960795 + 4933162 * 2 ^ 59
def prefixEnd_4933162 : Nat := 4983230072969 + 3 ^ 40 * 4933162 * 2
def baseEnd_4933162 : Nat := 2533083252495333214687807

theorem tailTrace_4933162 : CollatzResearch.WordTrace tailWord_4933162 prefixEnd_4933162 2533083252495333214687807 := by
  unfold tailWord_4933162
  simp only [CollatzResearch.WordTrace]
  refine ⟨44981799938501016459626435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119951466502669377225670493 44981799938501016459626435)
  ·
    refine ⟨67472699907751524689439653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44981799938501016459626435 67472699907751524689439653)
    ·
      refine ⟨12651131232703410879269935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67472699907751524689439653 12651131232703410879269935)
      ·
        refine ⟨18976696849055116318904903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12651131232703410879269935 18976696849055116318904903)
        ·
          refine ⟨28465045273582674478357355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18976696849055116318904903 28465045273582674478357355)
          ·
            refine ⟨42697567910374011717536033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28465045273582674478357355 42697567910374011717536033)
            ·
              refine ⟨32023175932780508788152025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42697567910374011717536033 32023175932780508788152025)
              ·
                refine ⟨24017381949585381591114019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32023175932780508788152025 24017381949585381591114019)
                ·
                  refine ⟨36026072924378072386671029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24017381949585381591114019 36026072924378072386671029)
                  ·
                    refine ⟨3377444336660444286250409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36026072924378072386671029 3377444336660444286250409)
                    ·
                      refine ⟨2533083252495333214687807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377444336660444286250409 2533083252495333214687807)
                      ·
                        rfl

theorem cell23_4933162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4933162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933162 prefixEnd_4933162 := by exact prefixLift 4933162
  have htrace : WordTrace (prefixWord ++ tailWord_4933162) baseStart_4933162 baseEnd_4933162 := by
    simpa [prefixWord, tailWord_4933162, baseEnd_4933162] using wordTrace_append hprefix tailTrace_4933162
  have hstable : (prefixWord ++ tailWord_4933162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933162).length < 2 ^ (prefixWord ++ tailWord_4933162).sum := by decide
  have hdescent : baseEnd_4933162 < baseStart_4933162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933175 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_4933175 : Nat := 118140960795 + 4933175 * 2 ^ 59
def prefixEnd_4933175 : Nat := 4983230072969 + 3 ^ 40 * 4933175 * 2
def baseEnd_4933175 : Nat := 2533089927743841663825247

theorem tailTrace_4933175 : CollatzResearch.WordTrace tailWord_4933175 prefixEnd_4933175 2533089927743841663825247 := by
  unfold tailWord_4933175
  simp only [CollatzResearch.WordTrace]
  refine ⟨179927673902956969058728979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119951782601971312705819319 179927673902956969058728979)
  ·
    refine ⟨269891510854435453588093469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179927673902956969058728979 269891510854435453588093469)
    ·
      refine ⟨101209316570413295095535051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269891510854435453588093469 101209316570413295095535051)
      ·
        refine ⟨151813974855619942643302577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101209316570413295095535051 151813974855619942643302577)
        ·
          refine ⟨113860481141714956982476933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151813974855619942643302577 113860481141714956982476933)
          ·
            refine ⟨21348840214071554434214425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113860481141714956982476933 21348840214071554434214425)
            ·
              refine ⟨16011630160553665825660819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21348840214071554434214425 16011630160553665825660819)
              ·
                refine ⟨24017445240830498738491229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16011630160553665825660819 24017445240830498738491229)
                ·
                  refine ⟨9006541965311437026934211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24017445240830498738491229 9006541965311437026934211)
                  ·
                    refine ⟨13509812947967155540401317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9006541965311437026934211 13509812947967155540401317)
                    ·
                      refine ⟨2533089927743841663825247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13509812947967155540401317 2533089927743841663825247)
                      ·
                        rfl

theorem cell23_4933175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_4933175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933175 prefixEnd_4933175 := by exact prefixLift 4933175
  have htrace : WordTrace (prefixWord ++ tailWord_4933175) baseStart_4933175 baseEnd_4933175 := by
    simpa [prefixWord, tailWord_4933175, baseEnd_4933175] using wordTrace_append hprefix tailTrace_4933175
  have hstable : (prefixWord ++ tailWord_4933175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933175).length < 2 ^ (prefixWord ++ tailWord_4933175).sum := by decide
  have hdescent : baseEnd_4933175 < baseStart_4933175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933185 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4933185 : Nat := 118140960795 + 4933185 * 2 ^ 59
def prefixEnd_4933185 : Nat := 4983230072969 + 3 ^ 40 * 4933185 * 2
def baseEnd_4933185 : Nat := 844365020850128874900067

theorem tailTrace_4933185 : CollatzResearch.WordTrace tailWord_4933185 prefixEnd_4933185 844365020850128874900067 := by
  unfold tailWord_4933185
  simp only [CollatzResearch.WordTrace]
  refine ⟨179928038632920740766593009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119952025755280493844395339 179928038632920740766593009)
  ·
    refine ⟨134946028974690555574944757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179928038632920740766593009 134946028974690555574944757)
    ·
      refine ⟨12651190216377239585151071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134946028974690555574944757 12651190216377239585151071)
      ·
        refine ⟨18976785324565859377726607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12651190216377239585151071 18976785324565859377726607)
        ·
          refine ⟨28465177986848789066589911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18976785324565859377726607 28465177986848789066589911)
          ·
            refine ⟨42697766980273183599884867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28465177986848789066589911 42697766980273183599884867)
            ·
              refine ⟨64046650470409775399827301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42697766980273183599884867 64046650470409775399827301)
              ·
                refine ⟨12008746963201832887467619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64046650470409775399827301 12008746963201832887467619)
                ·
                  refine ⟨18013120444802749331201429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12008746963201832887467619 18013120444802749331201429)
                  ·
                    refine ⟨844365020850128874900067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18013120444802749331201429 844365020850128874900067)
                    ·
                      rfl

theorem cell23_4933185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4933185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933185 prefixEnd_4933185 := by exact prefixLift 4933185
  have htrace : WordTrace (prefixWord ++ tailWord_4933185) baseStart_4933185 baseEnd_4933185 := by
    simpa [prefixWord, tailWord_4933185, baseEnd_4933185] using wordTrace_append hprefix tailTrace_4933185
  have hstable : (prefixWord ++ tailWord_4933185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933185).length < 2 ^ (prefixWord ++ tailWord_4933185).sum := by decide
  have hdescent : baseEnd_4933185 < baseStart_4933185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933202 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_4933202 : Nat := 118140960795 + 4933202 * 2 ^ 59
def prefixEnd_4933202 : Nat := 4983230072969 + 3 ^ 40 * 4933202 * 2
def baseEnd_4933202 : Nat := 844367930573837686062541

theorem tailTrace_4933202 : CollatzResearch.WordTrace tailWord_4933202 prefixEnd_4933202 844367930573837686062541 := by
  unfold tailWord_4933202
  simp only [CollatzResearch.WordTrace]
  refine ⟨44982164668464788167490465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119952439115906101779974573 44982164668464788167490465)
  ·
    refine ⟨33736623501348591125617849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44982164668464788167490465 33736623501348591125617849)
    ·
      refine ⟨25302467626011443344213387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33736623501348591125617849 25302467626011443344213387)
      ·
        refine ⟨37953701439017165016320081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25302467626011443344213387 37953701439017165016320081)
        ·
          refine ⟨28465276079262873762240061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37953701439017165016320081 28465276079262873762240061)
          ·
            refine ⟨10674478529723577660840023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28465276079262873762240061 10674478529723577660840023)
            ·
              refine ⟨16011717794585366491260035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674478529723577660840023 16011717794585366491260035)
              ·
                refine ⟨24017576691878049736890053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16011717794585366491260035 24017576691878049736890053)
                ·
                  refine ⟨4503295629727134325666885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24017576691878049736890053 4503295629727134325666885)
                  ·
                    refine ⟨844367930573837686062541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503295629727134325666885 844367930573837686062541)
                    ·
                      rfl

theorem cell23_4933202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_4933202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933202 prefixEnd_4933202 := by exact prefixLift 4933202
  have htrace : WordTrace (prefixWord ++ tailWord_4933202) baseStart_4933202 baseEnd_4933202 := by
    simpa [prefixWord, tailWord_4933202, baseEnd_4933202] using wordTrace_append hprefix tailTrace_4933202
  have hstable : (prefixWord ++ tailWord_4933202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933202).length < 2 ^ (prefixWord ++ tailWord_4933202).sum := by decide
  have hdescent : baseEnd_4933202 < baseStart_4933202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933208 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_4933208 : Nat := 118140960795 + 4933208 * 2 ^ 59
def prefixEnd_4933208 : Nat := 4983230072969 + 3 ^ 40 * 4933208 * 2
def baseEnd_4933208 : Nat := 2533106872605440034712595

theorem tailTrace_4933208 : CollatzResearch.WordTrace tailWord_4933208 prefixEnd_4933208 2533106872605440034712595 := by
  unfold tailWord_4933208
  simp only [CollatzResearch.WordTrace]
  refine ⟨89964438755918707847340139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119952585007891610463120185 89964438755918707847340139)
  ·
    refine ⟨134946658133878061771010209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89964438755918707847340139 134946658133878061771010209)
    ·
      refine ⟨101209993600408546328257657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134946658133878061771010209 101209993600408546328257657)
      ·
        refine ⟨75907495200306409746193243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101209993600408546328257657 75907495200306409746193243)
        ·
          refine ⟨113861242800459614619289865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75907495200306409746193243 113861242800459614619289865)
          ·
            refine ⟨85395932100344710964467399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113861242800459614619289865 85395932100344710964467399)
            ·
              refine ⟨128093898150517066446701099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85395932100344710964467399 128093898150517066446701099)
              ·
                refine ⟨192140847225775599670051649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128093898150517066446701099 192140847225775599670051649)
                ·
                  refine ⟨144105635419331699752538737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192140847225775599670051649 144105635419331699752538737)
                  ·
                    refine ⟨108079226564498774814404053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144105635419331699752538737 108079226564498774814404053)
                    ·
                      refine ⟨2533106872605440034712595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108079226564498774814404053 2533106872605440034712595)
                      ·
                        rfl

theorem cell23_4933208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_4933208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933208 prefixEnd_4933208 := by exact prefixLift 4933208
  have htrace : WordTrace (prefixWord ++ tailWord_4933208) baseStart_4933208 baseEnd_4933208 := by
    simpa [prefixWord, tailWord_4933208, baseEnd_4933208] using wordTrace_append hprefix tailTrace_4933208
  have hstable : (prefixWord ++ tailWord_4933208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933208).length < 2 ^ (prefixWord ++ tailWord_4933208).sum := by decide
  have hdescent : baseEnd_4933208 < baseStart_4933208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933212 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4933212 : Nat := 118140960795 + 4933212 * 2 ^ 59
def prefixEnd_4933212 : Nat := 4983230072969 + 3 ^ 40 * 4933212 * 2
def baseEnd_4933212 : Nat := 2533108926528058019062577

theorem tailTrace_4933212 : CollatzResearch.WordTrace tailWord_4933212 prefixEnd_4933212 2533108926528058019062577 := by
  unfold tailWord_4933212
  simp only [CollatzResearch.WordTrace]
  refine ⟨89964511701911462188912945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119952682269215282918550593 89964511701911462188912945)
  ·
    refine ⟨67473383776433596641684709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89964511701911462188912945 67473383776433596641684709)
    ·
      refine ⟨12651259458081299370315883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67473383776433596641684709 12651259458081299370315883)
      ·
        refine ⟨18976889187121949055473825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12651259458081299370315883 18976889187121949055473825)
        ·
          refine ⟨14232666890341461791605369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18976889187121949055473825 14232666890341461791605369)
          ·
            refine ⟨10674500167756096343704027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14232666890341461791605369 10674500167756096343704027)
            ·
              refine ⟨16011750251634144515556041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674500167756096343704027 16011750251634144515556041)
              ·
                refine ⟨12008812688725608386667031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16011750251634144515556041 12008812688725608386667031)
                ·
                  refine ⟨18013219033088412580000547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12008812688725608386667031 18013219033088412580000547)
                  ·
                    refine ⟨27019828549632618870000821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18013219033088412580000547 27019828549632618870000821)
                    ·
                      refine ⟨2533108926528058019062577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27019828549632618870000821 2533108926528058019062577)
                      ·
                        rfl

theorem cell23_4933212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4933212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933212 prefixEnd_4933212 := by exact prefixLift 4933212
  have htrace : WordTrace (prefixWord ++ tailWord_4933212) baseStart_4933212 baseEnd_4933212 := by
    simpa [prefixWord, tailWord_4933212, baseEnd_4933212] using wordTrace_append hprefix tailTrace_4933212
  have hstable : (prefixWord ++ tailWord_4933212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933212).length < 2 ^ (prefixWord ++ tailWord_4933212).sum := by decide
  have hdescent : baseEnd_4933212 < baseStart_4933212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933219 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 2, 4]
def baseStart_4933219 : Nat := 118140960795 + 4933219 * 2 ^ 59
def prefixEnd_4933219 : Nat := 4983230072969 + 3 ^ 40 * 4933219 * 2
def baseEnd_4933219 : Nat := 844370840297546497225015

theorem tailTrace_4933219 : CollatzResearch.WordTrace tailWord_4933219 prefixEnd_4933219 844370840297546497225015 := by
  unfold tailWord_4933219
  simp only [CollatzResearch.WordTrace]
  refine ⟨179929278714797564573330711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119952852476531709715553807 179929278714797564573330711)
  ·
    refine ⟨269893918072196346859996067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179929278714797564573330711 269893918072196346859996067)
    ·
      refine ⟨404840877108294520289994101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269893918072196346859996067 404840877108294520289994101)
      ·
        refine ⟨37953832228902611277186947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 404840877108294520289994101 37953832228902611277186947)
        ·
          refine ⟨56930748343353916915780421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37953832228902611277186947 56930748343353916915780421)
          ·
            refine ⟨10674515314378859421708829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56930748343353916915780421 10674515314378859421708829)
            ·
              refine ⟨4002943242892072283140811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10674515314378859421708829 4002943242892072283140811)
              ·
                refine ⟨6004414864338108424711217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002943242892072283140811 6004414864338108424711217)
                ·
                  refine ⟨4503311148253581318533413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004414864338108424711217 4503311148253581318533413)
                  ·
                    refine ⟨844370840297546497225015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503311148253581318533413 844370840297546497225015)
                    ·
                      rfl

theorem cell23_4933219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 4].length) (baseStart_4933219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933219 prefixEnd_4933219 := by exact prefixLift 4933219
  have htrace : WordTrace (prefixWord ++ tailWord_4933219) baseStart_4933219 baseEnd_4933219 := by
    simpa [prefixWord, tailWord_4933219, baseEnd_4933219] using wordTrace_append hprefix tailTrace_4933219
  have hstable : (prefixWord ++ tailWord_4933219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933219).length < 2 ^ (prefixWord ++ tailWord_4933219).sum := by decide
  have hdescent : baseEnd_4933219 < baseStart_4933219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933232 : List Nat := [2, 1, 1, 1, 6, 3, 2, 7]
def baseStart_4933232 : Nat := 118140960795 + 4933232 * 2 ^ 59
def prefixEnd_4933232 : Nat := 4983230072969 + 3 ^ 40 * 4933232 * 2
def baseEnd_4933232 : Nat := 93819229486709182993055

theorem tailTrace_4933232 : CollatzResearch.WordTrace tailWord_4933232 prefixEnd_4933232 93819229486709182993055 := by
  unfold tailWord_4933232
  simp only [CollatzResearch.WordTrace]
  refine ⟨89964876431875233896776975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119953168575833645195702633 89964876431875233896776975)
  ·
    refine ⟨134947314647812850845165463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89964876431875233896776975 134947314647812850845165463)
    ·
      refine ⟨202420971971719276267748195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134947314647812850845165463 202420971971719276267748195)
      ·
        refine ⟨303631457957578914401622293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202420971971719276267748195 303631457957578914401622293)
        ·
          refine ⟨14232724591761511612576045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 303631457957578914401622293 14232724591761511612576045)
          ·
            refine ⟨5337271721910566854716017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14232724591761511612576045 5337271721910566854716017)
            ·
              refine ⟨4002953791432925141037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5337271721910566854716017 4002953791432925141037013)
              ·
                refine ⟨93819229486709182993055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4002953791432925141037013 93819229486709182993055)
                ·
                  rfl

theorem cell23_4933232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 7].length) (baseStart_4933232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933232 prefixEnd_4933232 := by exact prefixLift 4933232
  have htrace : WordTrace (prefixWord ++ tailWord_4933232) baseStart_4933232 baseEnd_4933232 := by
    simpa [prefixWord, tailWord_4933232, baseEnd_4933232] using wordTrace_append hprefix tailTrace_4933232
  have hstable : (prefixWord ++ tailWord_4933232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933232).length < 2 ^ (prefixWord ++ tailWord_4933232).sum := by decide
  have hdescent : baseEnd_4933232 < baseStart_4933232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933276 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4933276 : Nat := 118140960795 + 4933276 * 2 ^ 59
def prefixEnd_4933276 : Nat := 4983230072969 + 3 ^ 40 * 4933276 * 2
def baseEnd_4933276 : Nat := 2533141789289945768662283

theorem tailTrace_4933276 : CollatzResearch.WordTrace tailWord_4933276 prefixEnd_4933276 2533141789289945768662283 := by
  unfold tailWord_4933276
  simp only [CollatzResearch.WordTrace]
  refine ⟨89965678837795531654077841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119954238450394042205437121 89965678837795531654077841)
  ·
    refine ⟨67474259128346648740558381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89965678837795531654077841 67474259128346648740558381)
    ·
      refine ⟨25302847173129993277709393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67474259128346648740558381 25302847173129993277709393)
      ·
        refine ⟨18977135379847494958282045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25302847173129993277709393 18977135379847494958282045)
        ·
          refine ⟨7116425767442810609355767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18977135379847494958282045 7116425767442810609355767)
          ·
            refine ⟨10674638651164215914033651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7116425767442810609355767 10674638651164215914033651)
            ·
              refine ⟨16011957976746323871050477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674638651164215914033651 16011957976746323871050477)
              ·
                refine ⟨6004484241279871451643929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16011957976746323871050477 6004484241279871451643929)
                ·
                  refine ⟨4503363180959903588732947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6004484241279871451643929 4503363180959903588732947)
                  ·
                    refine ⟨6755044771439855383099421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503363180959903588732947 6755044771439855383099421)
                    ·
                      refine ⟨2533141789289945768662283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755044771439855383099421 2533141789289945768662283)
                      ·
                        rfl

theorem cell23_4933276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4933276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933276 prefixEnd_4933276 := by exact prefixLift 4933276
  have htrace : WordTrace (prefixWord ++ tailWord_4933276) baseStart_4933276 baseEnd_4933276 := by
    simpa [prefixWord, tailWord_4933276, baseEnd_4933276] using wordTrace_append hprefix tailTrace_4933276
  have hstable : (prefixWord ++ tailWord_4933276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933276).length < 2 ^ (prefixWord ++ tailWord_4933276).sum := by decide
  have hdescent : baseEnd_4933276 < baseStart_4933276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933285 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_4933285 : Nat := 118140960795 + 4933285 * 2 ^ 59
def prefixEnd_4933285 : Nat := 4983230072969 + 3 ^ 40 * 4933285 * 2
def baseEnd_4933285 : Nat := 2533146410615836233449741

theorem tailTrace_4933285 : CollatzResearch.WordTrace tailWord_4933285 prefixEnd_4933285 2533146410615836233449741 := by
  unfold tailWord_4933285
  simp only [CollatzResearch.WordTrace]
  refine ⟨179931685932558457845233309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119954457288372305230155539 179931685932558457845233309)
  ·
    refine ⟨67474382224709421691962491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179931685932558457845233309 67474382224709421691962491)
    ·
      refine ⟨101211573337064132537943737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67474382224709421691962491 101211573337064132537943737)
      ·
        refine ⟨75908680002798099403457803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101211573337064132537943737 75908680002798099403457803)
        ·
          refine ⟨113863020004197149105186705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75908680002798099403457803 113863020004197149105186705)
          ·
            refine ⟨85397265003147861828890029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113863020004197149105186705 85397265003147861828890029)
            ·
              refine ⟨32023974376180448185833761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85397265003147861828890029 32023974376180448185833761)
              ·
                refine ⟨24017980782135336139375321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32023974376180448185833761 24017980782135336139375321)
                ·
                  refine ⟨18013485586601502104531491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24017980782135336139375321 18013485586601502104531491)
                  ·
                    refine ⟨27020228379902253156797237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18013485586601502104531491 27020228379902253156797237)
                    ·
                      refine ⟨2533146410615836233449741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27020228379902253156797237 2533146410615836233449741)
                      ·
                        rfl

theorem cell23_4933285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_4933285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933285 prefixEnd_4933285 := by exact prefixLift 4933285
  have htrace : WordTrace (prefixWord ++ tailWord_4933285) baseStart_4933285 baseEnd_4933285 := by
    simpa [prefixWord, tailWord_4933285, baseEnd_4933285] using wordTrace_append hprefix tailTrace_4933285
  have hstable : (prefixWord ++ tailWord_4933285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933285).length < 2 ^ (prefixWord ++ tailWord_4933285).sum := by decide
  have hdescent : baseEnd_4933285 < baseStart_4933285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933315 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3]
def baseStart_4933315 : Nat := 118140960795 + 4933315 * 2 ^ 59
def prefixEnd_4933315 : Nat := 4983230072969 + 3 ^ 40 * 4933315 * 2
def baseEnd_4933315 : Nat := 2533161815035471116074603

theorem tailTrace_4933315 : CollatzResearch.WordTrace tailWord_4933315 prefixEnd_4933315 2533161815035471116074603 := by
  unfold tailWord_4933315
  simp only [CollatzResearch.WordTrace]
  refine ⟨179932780122449772968825399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119955186748299848645883599 179932780122449772968825399)
  ·
    refine ⟨269899170183674659453238099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179932780122449772968825399 269899170183674659453238099)
    ·
      refine ⟨404848755275511989179857149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269899170183674659453238099 404848755275511989179857149)
      ·
        refine ⟨151818283228316995942446431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404848755275511989179857149 151818283228316995942446431)
        ·
          refine ⟨227727424842475493913669647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151818283228316995942446431 227727424842475493913669647)
          ·
            refine ⟨341591137263713240870504471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227727424842475493913669647 341591137263713240870504471)
            ·
              refine ⟨512386705895569861305756707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341591137263713240870504471 512386705895569861305756707)
              ·
                refine ⟨768580058843354791958635061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512386705895569861305756707 768580058843354791958635061)
                ·
                  refine ⟨72054380516564511746122037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 768580058843354791958635061 72054380516564511746122037)
                  ·
                    refine ⟨6755098173427922976198941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72054380516564511746122037 6755098173427922976198941)
                    ·
                      refine ⟨2533161815035471116074603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755098173427922976198941 2533161815035471116074603)
                      ·
                        rfl

theorem cell23_4933315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_4933315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933315 prefixEnd_4933315 := by exact prefixLift 4933315
  have htrace : WordTrace (prefixWord ++ tailWord_4933315) baseStart_4933315 baseEnd_4933315 := by
    simpa [prefixWord, tailWord_4933315, baseEnd_4933315] using wordTrace_append hprefix tailTrace_4933315
  have hstable : (prefixWord ++ tailWord_4933315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933315).length < 2 ^ (prefixWord ++ tailWord_4933315).sum := by decide
  have hdescent : baseEnd_4933315 < baseStart_4933315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933335 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 7]
def baseStart_4933335 : Nat := 118140960795 + 4933335 * 2 ^ 59
def prefixEnd_4933335 : Nat := 4983230072969 + 3 ^ 40 * 4933335 * 2
def baseEnd_4933335 : Nat := 844390694882853679274837

theorem tailTrace_4933335 : CollatzResearch.WordTrace tailWord_4933335 prefixEnd_4933335 844390694882853679274837 := by
  unfold tailWord_4933335
  simp only [CollatzResearch.WordTrace]
  refine ⟨179933509582377316384553459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119955673054918210923035639 179933509582377316384553459)
  ·
    refine ⟨269900264373565974576830189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179933509582377316384553459 269900264373565974576830189)
    ·
      refine ⟨101212599140087240466311321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269900264373565974576830189 101212599140087240466311321)
      ·
        refine ⟨75909449355065430349733491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101212599140087240466311321 75909449355065430349733491)
        ·
          refine ⟨113864174032598145524600237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75909449355065430349733491 113864174032598145524600237)
          ·
            refine ⟨42699065262224304571725089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113864174032598145524600237 42699065262224304571725089)
            ·
              refine ⟨32024298946668228428793817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42699065262224304571725089 32024298946668228428793817)
              ·
                refine ⟨24018224210001171321595363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32024298946668228428793817 24018224210001171321595363)
                ·
                  refine ⟨36027336315001756982393045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24018224210001171321595363 36027336315001756982393045)
                  ·
                    refine ⟨844390694882853679274837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36027336315001756982393045 844390694882853679274837)
                    ·
                      rfl

theorem cell23_4933335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_4933335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933335 prefixEnd_4933335 := by exact prefixLift 4933335
  have htrace : WordTrace (prefixWord ++ tailWord_4933335) baseStart_4933335 baseEnd_4933335 := by
    simpa [prefixWord, tailWord_4933335, baseEnd_4933335] using wordTrace_append hprefix tailTrace_4933335
  have hstable : (prefixWord ++ tailWord_4933335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933335).length < 2 ^ (prefixWord ++ tailWord_4933335).sum := by decide
  have hdescent : baseEnd_4933335 < baseStart_4933335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933352 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_4933352 : Nat := 118140960795 + 4933352 * 2 ^ 59
def prefixEnd_4933352 : Nat := 4983230072969 + 3 ^ 40 * 4933352 * 2
def baseEnd_4933352 : Nat := 844393604606562490437311

theorem tailTrace_4933352 : CollatzResearch.WordTrace tailWord_4933352 prefixEnd_4933352 844393604606562490437311 := by
  unfold tailWord_4933352
  simp only [CollatzResearch.WordTrace]
  refine ⟨89967064811657864143961155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119956086415543818858614873 89967064811657864143961155)
  ·
    refine ⟨134950597217486796215941733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89967064811657864143961155 134950597217486796215941733)
    ·
      refine ⟨25303236978278774290489075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134950597217486796215941733 25303236978278774290489075)
      ·
        refine ⟨37954855467418161435733613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25303236978278774290489075 37954855467418161435733613)
        ·
          refine ⟨14233070800281810538400105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37954855467418161435733613 14233070800281810538400105)
          ·
            refine ⟨10674803100211357903800079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14233070800281810538400105 10674803100211357903800079)
            ·
              refine ⟨16012204650317036855700119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674803100211357903800079 16012204650317036855700119)
              ·
                refine ⟨24018306975475555283550179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16012204650317036855700119 24018306975475555283550179)
                ·
                  refine ⟨36027460463213332925325269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24018306975475555283550179 36027460463213332925325269)
                  ·
                    refine ⟨844393604606562490437311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36027460463213332925325269 844393604606562490437311)
                    ·
                      rfl

theorem cell23_4933352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_4933352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933352 prefixEnd_4933352 := by exact prefixLift 4933352
  have htrace : WordTrace (prefixWord ++ tailWord_4933352) baseStart_4933352 baseEnd_4933352 := by
    simpa [prefixWord, tailWord_4933352, baseEnd_4933352] using wordTrace_append hprefix tailTrace_4933352
  have hstable : (prefixWord ++ tailWord_4933352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933352).length < 2 ^ (prefixWord ++ tailWord_4933352).sum := by decide
  have hdescent : baseEnd_4933352 < baseStart_4933352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933372 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_4933372 : Nat := 118140960795 + 4933372 * 2 ^ 59
def prefixEnd_4933372 : Nat := 4983230072969 + 3 ^ 40 * 4933372 * 2
def baseEnd_4933372 : Nat := 2533191083432777393061841

theorem tailTrace_4933372 : CollatzResearch.WordTrace tailWord_4933372 prefixEnd_4933372 2533191083432777393061841 := by
  unfold tailWord_4933372
  simp only [CollatzResearch.WordTrace]
  refine ⟨89967429541621635851825185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119956572722162181135766913 89967429541621635851825185)
  ·
    refine ⟨67475572156216226888868889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89967429541621635851825185 67475572156216226888868889)
    ·
      refine ⟨50606679117162170166651667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67475572156216226888868889 50606679117162170166651667)
      ·
        refine ⟨75910018675743255249977501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50606679117162170166651667 75910018675743255249977501)
        ·
          refine ⟨28466257003403720718741563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75910018675743255249977501 28466257003403720718741563)
          ·
            refine ⟨42699385505105581078112345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28466257003403720718741563 42699385505105581078112345)
            ·
              refine ⟨32024539128829185808584259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42699385505105581078112345 32024539128829185808584259)
              ·
                refine ⟨48036808693243778712876389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32024539128829185808584259 48036808693243778712876389)
                ·
                  refine ⟨9006901629983208508664323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48036808693243778712876389 9006901629983208508664323)
                  ·
                    refine ⟨13510352444974812762996485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9006901629983208508664323 13510352444974812762996485)
                    ·
                      refine ⟨2533191083432777393061841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13510352444974812762996485 2533191083432777393061841)
                      ·
                        rfl

theorem cell23_4933372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_4933372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933372 prefixEnd_4933372 := by exact prefixLift 4933372
  have htrace : WordTrace (prefixWord ++ tailWord_4933372) baseStart_4933372 baseEnd_4933372 := by
    simpa [prefixWord, tailWord_4933372, baseEnd_4933372] using wordTrace_append hprefix tailTrace_4933372
  have hstable : (prefixWord ++ tailWord_4933372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933372).length < 2 ^ (prefixWord ++ tailWord_4933372).sum := by decide
  have hdescent : baseEnd_4933372 < baseStart_4933372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933375 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_4933375 : Nat := 118140960795 + 4933375 * 2 ^ 59
def prefixEnd_4933375 : Nat := 4983230072969 + 3 ^ 40 * 4933375 * 2
def baseEnd_4933375 : Nat := 2533192623874740881324327

theorem tailTrace_4933375 : CollatzResearch.WordTrace tailWord_4933375 prefixEnd_4933375 2533192623874740881324327 := by
  unfold tailWord_4933375
  simp only [CollatzResearch.WordTrace]
  refine ⟨179934968502232403216009579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119956645668154935477339719 179934968502232403216009579)
  ·
    refine ⟨269902452753348604824014369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179934968502232403216009579 269902452753348604824014369)
    ·
      refine ⟨202426839565011453618010777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269902452753348604824014369 202426839565011453618010777)
      ·
        refine ⟨151820129673758590213508083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202426839565011453618010777 151820129673758590213508083)
        ·
          refine ⟨227730194510637885320262125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151820129673758590213508083 227730194510637885320262125)
          ·
            refine ⟨85398822941489206995098297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227730194510637885320262125 85398822941489206995098297)
            ·
              refine ⟨64049117206116905246323723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85398822941489206995098297 64049117206116905246323723)
              ·
                refine ⟨96073675809175357869485585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64049117206116905246323723 96073675809175357869485585)
                ·
                  refine ⟨72055256856881518402114189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96073675809175357869485585 72055256856881518402114189)
                  ·
                    refine ⟨27020721321330569400792821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72055256856881518402114189 27020721321330569400792821)
                    ·
                      refine ⟨2533192623874740881324327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27020721321330569400792821 2533192623874740881324327)
                      ·
                        rfl

theorem cell23_4933375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_4933375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933375 prefixEnd_4933375 := by exact prefixLift 4933375
  have htrace : WordTrace (prefixWord ++ tailWord_4933375) baseStart_4933375 baseEnd_4933375 := by
    simpa [prefixWord, tailWord_4933375, baseEnd_4933375] using wordTrace_append hprefix tailTrace_4933375
  have hstable : (prefixWord ++ tailWord_4933375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933375).length < 2 ^ (prefixWord ++ tailWord_4933375).sum := by decide
  have hdescent : baseEnd_4933375 < baseStart_4933375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933385 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_4933385 : Nat := 118140960795 + 4933385 * 2 ^ 59
def prefixEnd_4933385 : Nat := 4983230072969 + 3 ^ 40 * 4933385 * 2
def baseEnd_4933385 : Nat := 2533197758681285842199281

theorem tailTrace_4933385 : CollatzResearch.WordTrace tailWord_4933385 prefixEnd_4933385 2533197758681285842199281 := by
  unfold tailWord_4933385
  simp only [CollatzResearch.WordTrace]
  refine ⟨179935333232196174923873609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119956888821464116615915739 179935333232196174923873609)
  ·
    refine ⟨134951499924147131192905207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179935333232196174923873609 134951499924147131192905207)
    ·
      refine ⟨202427249886220696789357811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134951499924147131192905207 202427249886220696789357811)
      ·
        refine ⟨303640874829331045184036717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202427249886220696789357811 303640874829331045184036717)
        ·
          refine ⟨113865328060999141944013769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303640874829331045184036717 113865328060999141944013769)
          ·
            refine ⟨85398996045749356458010327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113865328060999141944013769 85398996045749356458010327)
            ·
              refine ⟨128098494068624034687015491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85398996045749356458010327 128098494068624034687015491)
              ·
                refine ⟨192147741102936052030523237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128098494068624034687015491 192147741102936052030523237)
                ·
                  refine ⟨36027701456800509755723107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192147741102936052030523237 36027701456800509755723107)
                  ·
                    refine ⟨54041552185200764633584661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36027701456800509755723107 54041552185200764633584661)
                    ·
                      refine ⟨2533197758681285842199281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54041552185200764633584661 2533197758681285842199281)
                      ·
                        rfl

theorem cell23_4933385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_4933385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933385 prefixEnd_4933385 := by exact prefixLift 4933385
  have htrace : WordTrace (prefixWord ++ tailWord_4933385) baseStart_4933385 baseEnd_4933385 := by
    simpa [prefixWord, tailWord_4933385, baseEnd_4933385] using wordTrace_append hprefix tailTrace_4933385
  have hstable : (prefixWord ++ tailWord_4933385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933385).length < 2 ^ (prefixWord ++ tailWord_4933385).sum := by decide
  have hdescent : baseEnd_4933385 < baseStart_4933385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933399 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 3, 4]
def baseStart_4933399 : Nat := 118140960795 + 4933399 * 2 ^ 59
def prefixEnd_4933399 : Nat := 4983230072969 + 3 ^ 40 * 4933399 * 2
def baseEnd_4933399 : Nat := 844401649136816262474739

theorem tailTrace_4933399 : CollatzResearch.WordTrace tailWord_4933399 prefixEnd_4933399 844401649136816262474739 := by
  unfold tailWord_4933399
  simp only [CollatzResearch.WordTrace]
  refine ⟨179935843854145455314883251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119957229236096970209922167 179935843854145455314883251)
  ·
    refine ⟨269903765781218182972324877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179935843854145455314883251 269903765781218182972324877)
    ·
      refine ⟨101213912167956818614621829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269903765781218182972324877 101213912167956818614621829)
      ·
        refine ⟨18977608531491903490241593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101213912167956818614621829 18977608531491903490241593)
        ·
          refine ⟨14233206398618927617681195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18977608531491903490241593 14233206398618927617681195)
          ·
            refine ⟨21349809597928391426521793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14233206398618927617681195 21349809597928391426521793)
            ·
              refine ⟨16012357198446293569891345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21349809597928391426521793 16012357198446293569891345)
              ·
                refine ⟨12009267898834720177418509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16012357198446293569891345 12009267898834720177418509)
                ·
                  refine ⟨4503475462063020066531941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12009267898834720177418509 4503475462063020066531941)
                  ·
                    refine ⟨844401649136816262474739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503475462063020066531941 844401649136816262474739)
                    ·
                      rfl

theorem cell23_4933399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_4933399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933399 prefixEnd_4933399 := by exact prefixLift 4933399
  have htrace : WordTrace (prefixWord ++ tailWord_4933399) baseStart_4933399 baseEnd_4933399 := by
    simpa [prefixWord, tailWord_4933399, baseEnd_4933399] using wordTrace_append hprefix tailTrace_4933399
  have hstable : (prefixWord ++ tailWord_4933399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933399).length < 2 ^ (prefixWord ++ tailWord_4933399).sum := by decide
  have hdescent : baseEnd_4933399 < baseStart_4933399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933412 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 8]
def baseStart_4933412 : Nat := 118140960795 + 4933412 * 2 ^ 59
def prefixEnd_4933412 : Nat := 4983230072969 + 3 ^ 40 * 4933412 * 2
def baseEnd_4933412 : Nat := 281467958073217470729073

theorem tailTrace_4933412 : CollatzResearch.WordTrace tailWord_4933412 prefixEnd_4933412 281467958073217470729073 := by
  unfold tailWord_4933412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89968159001549179267553245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119957545335398905690070993 89968159001549179267553245)
  ·
    refine ⟨33738059625580942225332467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89968159001549179267553245 33738059625580942225332467)
    ·
      refine ⟨50607089438371413337998701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33738059625580942225332467 50607089438371413337998701)
      ·
        refine ⟨18977658539389280001749513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50607089438371413337998701 18977658539389280001749513)
        ·
          refine ⟨14233243904541960001312135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18977658539389280001749513 14233243904541960001312135)
          ·
            refine ⟨21349865856812940001968203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14233243904541960001312135 21349865856812940001968203)
            ·
              refine ⟨32024798785219410002952305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21349865856812940001968203 32024798785219410002952305)
              ·
                refine ⟨24018599088914557502214229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32024798785219410002952305 24018599088914557502214229)
                ·
                  refine ⟨281467958073217470729073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24018599088914557502214229 281467958073217470729073)
                  ·
                    rfl

theorem cell23_4933412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_4933412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933412 prefixEnd_4933412 := by exact prefixLift 4933412
  have htrace : WordTrace (prefixWord ++ tailWord_4933412) baseStart_4933412 baseEnd_4933412 := by
    simpa [prefixWord, tailWord_4933412, baseEnd_4933412] using wordTrace_append hprefix tailTrace_4933412
  have hstable : (prefixWord ++ tailWord_4933412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933412).length < 2 ^ (prefixWord ++ tailWord_4933412).sum := by decide
  have hdescent : baseEnd_4933412 < baseStart_4933412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933433 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_4933433 : Nat := 118140960795 + 4933433 * 2 ^ 59
def prefixEnd_4933433 : Nat := 4983230072969 + 3 ^ 40 * 4933433 * 2
def baseEnd_4933433 : Nat := 844407468584233884799687

theorem tailTrace_4933433 : CollatzResearch.WordTrace tailWord_4933433 prefixEnd_4933433 844407468584233884799687 := by
  unfold tailWord_4933433
  simp only [CollatzResearch.WordTrace]
  refine ⟨179937083936022279121620953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119958055957348186081080635 179937083936022279121620953)
  ·
    refine ⟨134952812952016709341215715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179937083936022279121620953 134952812952016709341215715)
    ·
      refine ⟨202429219428025064011823573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134952812952016709341215715 202429219428025064011823573)
      ·
        refine ⟨4744434830344337437777115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 202429219428025064011823573 4744434830344337437777115)
        ·
          refine ⟨7116652245516506156665673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744434830344337437777115 7116652245516506156665673)
          ·
            refine ⟨5337489184137379617499255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7116652245516506156665673 5337489184137379617499255)
            ·
              refine ⟨8006233776206069426248883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337489184137379617499255 8006233776206069426248883)
              ·
                refine ⟨12009350664309104139373325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006233776206069426248883 12009350664309104139373325)
                ·
                  refine ⟨4503506499115914052264997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12009350664309104139373325 4503506499115914052264997)
                  ·
                    refine ⟨844407468584233884799687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503506499115914052264997 844407468584233884799687)
                    ·
                      rfl

theorem cell23_4933433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_4933433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933433 prefixEnd_4933433 := by exact prefixLift 4933433
  have htrace : WordTrace (prefixWord ++ tailWord_4933433) baseStart_4933433 baseEnd_4933433 := by
    simpa [prefixWord, tailWord_4933433, baseEnd_4933433] using wordTrace_append hprefix tailTrace_4933433
  have hstable : (prefixWord ++ tailWord_4933433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933433).length < 2 ^ (prefixWord ++ tailWord_4933433).sum := by decide
  have hdescent : baseEnd_4933433 < baseStart_4933433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933449 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 4, 3, 2]
def baseStart_4933449 : Nat := 118140960795 + 4933449 * 2 ^ 59
def prefixEnd_4933449 : Nat := 4983230072969 + 3 ^ 40 * 4933449 * 2
def baseEnd_4933449 : Nat := 2533230621443173591798987

theorem tailTrace_4933449 : CollatzResearch.WordTrace tailWord_4933449 prefixEnd_4933449 2533230621443173591798987 := by
  unfold tailWord_4933449
  simp only [CollatzResearch.WordTrace]
  refine ⟨179937667503964313854203401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119958445002642875902802267 179937667503964313854203401)
  ·
    refine ⟨134953250627973235390652551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179937667503964313854203401 134953250627973235390652551)
    ·
      refine ⟨202429875941959853085978827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134953250627973235390652551 202429875941959853085978827)
      ·
        refine ⟨303644813912939779628968241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202429875941959853085978827 303644813912939779628968241)
        ·
          refine ⟨227733610434704834721726181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303644813912939779628968241 227733610434704834721726181)
          ·
            refine ⟨42700051956507156510323659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227733610434704834721726181 42700051956507156510323659)
            ·
              refine ⟨64050077934760734765485489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42700051956507156510323659 64050077934760734765485489)
              ·
                refine ⟨48037558451070551074114117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64050077934760734765485489 48037558451070551074114117)
                ·
                  refine ⟨9007042209575728326396397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48037558451070551074114117 9007042209575728326396397)
                  ·
                    refine ⟨3377640828590898122398649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9007042209575728326396397 3377640828590898122398649)
                    ·
                      refine ⟨2533230621443173591798987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377640828590898122398649 2533230621443173591798987)
                      ·
                        rfl

theorem cell23_4933449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 3, 2].length) (baseStart_4933449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933449 prefixEnd_4933449 := by exact prefixLift 4933449
  have htrace : WordTrace (prefixWord ++ tailWord_4933449) baseStart_4933449 baseEnd_4933449 := by
    simpa [prefixWord, tailWord_4933449, baseEnd_4933449] using wordTrace_append hprefix tailTrace_4933449
  have hstable : (prefixWord ++ tailWord_4933449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933449).length < 2 ^ (prefixWord ++ tailWord_4933449).sum := by decide
  have hdescent : baseEnd_4933449 < baseStart_4933449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933466 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_4933466 : Nat := 118140960795 + 4933466 * 2 ^ 59
def prefixEnd_4933466 : Nat := 4983230072969 + 3 ^ 40 * 4933466 * 2
def baseEnd_4933466 : Nat := 2533239350614300025286409

theorem tailTrace_4933466 : CollatzResearch.WordTrace tailWord_4933466 prefixEnd_4933466 2533239350614300025286409 := by
  unfold tailWord_4933466
  simp only [CollatzResearch.WordTrace]
  refine ⟨44984571886225681439393063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119958858363268483838381501 44984571886225681439393063)
  ·
    refine ⟨67476857829338522159089595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44984571886225681439393063 67476857829338522159089595)
    ·
      refine ⟨101215286744007783238634393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67476857829338522159089595 101215286744007783238634393)
      ·
        refine ⟨75911465058005837428975795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101215286744007783238634393 75911465058005837428975795)
        ·
          refine ⟨113867197587008756143463693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75911465058005837428975795 113867197587008756143463693)
          ·
            refine ⟨42700199095128283553798885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113867197587008756143463693 42700199095128283553798885)
            ·
              refine ⟨8006287330336553166337291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42700199095128283553798885 8006287330336553166337291)
              ·
                refine ⟨12009430995504829749505937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006287330336553166337291 12009430995504829749505937)
                ·
                  refine ⟨9007073246628622312129453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12009430995504829749505937 9007073246628622312129453)
                  ·
                    refine ⟨3377652467485733367048545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9007073246628622312129453 3377652467485733367048545)
                    ·
                      refine ⟨2533239350614300025286409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377652467485733367048545 2533239350614300025286409)
                      ·
                        rfl

theorem cell23_4933466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_4933466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933466 prefixEnd_4933466 := by exact prefixLift 4933466
  have htrace : WordTrace (prefixWord ++ tailWord_4933466) baseStart_4933466 baseEnd_4933466 := by
    simpa [prefixWord, tailWord_4933466, baseEnd_4933466] using wordTrace_append hprefix tailTrace_4933466
  have hstable : (prefixWord ++ tailWord_4933466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933466).length < 2 ^ (prefixWord ++ tailWord_4933466).sum := by decide
  have hdescent : baseEnd_4933466 < baseStart_4933466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933472 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_4933472 : Nat := 118140960795 + 4933472 * 2 ^ 59
def prefixEnd_4933472 : Nat := 4983230072969 + 3 ^ 40 * 4933472 * 2
def baseEnd_4933472 : Nat := 844414143832742333937127

theorem tailTrace_4933472 : CollatzResearch.WordTrace tailWord_4933472 prefixEnd_4933472 844414143832742333937127 := by
  unfold tailWord_4933472
  simp only [CollatzResearch.WordTrace]
  refine ⟨89969253191440494391145335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119959004255253992521527113 89969253191440494391145335)
  ·
    refine ⟨134953879787160741586718003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89969253191440494391145335 134953879787160741586718003)
    ·
      refine ⟨202430819680741112380077005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134953879787160741586718003 202430819680741112380077005)
      ·
        refine ⟨75911557380277917142528877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202430819680741112380077005 75911557380277917142528877)
        ·
          refine ⟨28466834017604218928448329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75911557380277917142528877 28466834017604218928448329)
          ·
            refine ⟨21350125513203164196336247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28466834017604218928448329 21350125513203164196336247)
            ·
              refine ⟨32025188269804746294504371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21350125513203164196336247 32025188269804746294504371)
              ·
                refine ⟨48037782404707119441756557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32025188269804746294504371 48037782404707119441756557)
                ·
                  refine ⟨18014168401765169790658709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48037782404707119441756557 18014168401765169790658709)
                  ·
                    refine ⟨844414143832742333937127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18014168401765169790658709 844414143832742333937127)
                    ·
                      rfl

theorem cell23_4933472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_4933472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933472 prefixEnd_4933472 := by exact prefixLift 4933472
  have htrace : WordTrace (prefixWord ++ tailWord_4933472) baseStart_4933472 baseEnd_4933472 := by
    simpa [prefixWord, tailWord_4933472, baseEnd_4933472] using wordTrace_append hprefix tailTrace_4933472
  have hstable : (prefixWord ++ tailWord_4933472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933472).length < 2 ^ (prefixWord ++ tailWord_4933472).sum := by decide
  have hdescent : baseEnd_4933472 < baseStart_4933472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933509 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_4933509 : Nat := 118140960795 + 4933509 * 2 ^ 59
def prefixEnd_4933509 : Nat := 4983230072969 + 3 ^ 40 * 4933509 * 2
def baseEnd_4933509 : Nat := 2533261430282443357048711

theorem tailTrace_4933509 : CollatzResearch.WordTrace tailWord_4933509 prefixEnd_4933509 2533261430282443357048711 := by
  unfold tailWord_4933509
  simp only [CollatzResearch.WordTrace]
  refine ⟨179939855883746944101387581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119959903922497962734258387 179939855883746944101387581)
  ·
    refine ⟨67477445956405104038020343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179939855883746944101387581 67477445956405104038020343)
    ·
      refine ⟨101216168934607656057030515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67477445956405104038020343 101216168934607656057030515)
      ·
        refine ⟨151824253401911484085545773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101216168934607656057030515 151824253401911484085545773)
        ·
          refine ⟨56934095025716806532079665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151824253401911484085545773 56934095025716806532079665)
          ·
            refine ⟨42700571269287604899059749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56934095025716806532079665 42700571269287604899059749)
            ·
              refine ⟨8006357112991425918573703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42700571269287604899059749 8006357112991425918573703)
              ·
                refine ⟨12009535669487138877860555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006357112991425918573703 12009535669487138877860555)
                ·
                  refine ⟨18014303504230708316790833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12009535669487138877860555 18014303504230708316790833)
                  ·
                    refine ⟨13510727628173031237593125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18014303504230708316790833 13510727628173031237593125)
                    ·
                      refine ⟨2533261430282443357048711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13510727628173031237593125 2533261430282443357048711)
                      ·
                        rfl

theorem cell23_4933509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_4933509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933509 prefixEnd_4933509 := by exact prefixLift 4933509
  have htrace : WordTrace (prefixWord ++ tailWord_4933509) baseStart_4933509 baseEnd_4933509 := by
    simpa [prefixWord, tailWord_4933509, baseEnd_4933509] using wordTrace_append hprefix tailTrace_4933509
  have hstable : (prefixWord ++ tailWord_4933509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933509).length < 2 ^ (prefixWord ++ tailWord_4933509).sum := by decide
  have hdescent : baseEnd_4933509 < baseStart_4933509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933529 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_4933529 : Nat := 118140960795 + 4933529 * 2 ^ 59
def prefixEnd_4933529 : Nat := 4983230072969 + 3 ^ 40 * 4933529 * 2
def baseEnd_4933529 : Nat := 2533271699895533278798619

theorem tailTrace_4933529 : CollatzResearch.WordTrace tailWord_4933529 prefixEnd_4933529 2533271699895533278798619 := by
  unfold tailWord_4933529
  simp only [CollatzResearch.WordTrace]
  refine ⟨179940585343674487517115641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119960390229116325011410427 179940585343674487517115641)
  ·
    refine ⟨134955439007755865637836731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179940585343674487517115641 134955439007755865637836731)
    ·
      refine ⟨202433158511633798456755097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134955439007755865637836731 202433158511633798456755097)
      ·
        refine ⟨151824868883725348842566323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202433158511633798456755097 151824868883725348842566323)
        ·
          refine ⟨227737303325588023263849485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151824868883725348842566323 227737303325588023263849485)
          ·
            refine ⟨85401488747095508723943557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227737303325588023263849485 85401488747095508723943557)
            ·
              refine ⟨16012779140080407885739417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85401488747095508723943557 16012779140080407885739417)
              ·
                refine ⟨12009584355060305914304563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16012779140080407885739417 12009584355060305914304563)
                ·
                  refine ⟨18014376532590458871456845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12009584355060305914304563 18014376532590458871456845)
                  ·
                    refine ⟨6755391199721422076796317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18014376532590458871456845 6755391199721422076796317)
                    ·
                      refine ⟨2533271699895533278798619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755391199721422076796317 2533271699895533278798619)
                      ·
                        rfl

theorem cell23_4933529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_4933529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933529 prefixEnd_4933529 := by exact prefixLift 4933529
  have htrace : WordTrace (prefixWord ++ tailWord_4933529) baseStart_4933529 baseEnd_4933529 := by
    simpa [prefixWord, tailWord_4933529, baseEnd_4933529] using wordTrace_append hprefix tailTrace_4933529
  have hstable : (prefixWord ++ tailWord_4933529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933529).length < 2 ^ (prefixWord ++ tailWord_4933529).sum := by decide
  have hdescent : baseEnd_4933529 < baseStart_4933529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933530 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2]
def baseStart_4933530 : Nat := 118140960795 + 4933530 * 2 ^ 59
def prefixEnd_4933530 : Nat := 4983230072969 + 3 ^ 40 * 4933530 * 2
def baseEnd_4933530 : Nat := 2533272213376187774886115

theorem tailTrace_4933530 : CollatzResearch.WordTrace tailWord_4933530 prefixEnd_4933530 2533272213376187774886115 := by
  unfold tailWord_4933530
  simp only [CollatzResearch.WordTrace]
  refine ⟨44985155454167716171975511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119960414544447243125268029 44985155454167716171975511)
  ·
    refine ⟨67477733181251574257963267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44985155454167716171975511 67477733181251574257963267)
    ·
      refine ⟨101216599771877361386944901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67477733181251574257963267 101216599771877361386944901)
      ·
        refine ⟨18978112457227005260052169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101216599771877361386944901 18978112457227005260052169)
        ·
          refine ⟨14233584342920253945039127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18978112457227005260052169 14233584342920253945039127)
          ·
            refine ⟨21350376514380380917558691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14233584342920253945039127 21350376514380380917558691)
            ·
              refine ⟨32025564771570571376338037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21350376514380380917558691 32025564771570571376338037)
              ·
                refine ⟨3002396697334741066531691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32025564771570571376338037 3002396697334741066531691)
                ·
                  refine ⟨4503595046002111599797537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002396697334741066531691 4503595046002111599797537)
                  ·
                    refine ⟨3377696284501583699848153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4503595046002111599797537 3377696284501583699848153)
                    ·
                      refine ⟨2533272213376187774886115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377696284501583699848153 2533272213376187774886115)
                      ·
                        rfl

theorem cell23_4933530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_4933530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933530 prefixEnd_4933530 := by exact prefixLift 4933530
  have htrace : WordTrace (prefixWord ++ tailWord_4933530) baseStart_4933530 baseEnd_4933530 := by
    simpa [prefixWord, tailWord_4933530, baseEnd_4933530] using wordTrace_append hprefix tailTrace_4933530
  have hstable : (prefixWord ++ tailWord_4933530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933530).length < 2 ^ (prefixWord ++ tailWord_4933530).sum := by decide
  have hdescent : baseEnd_4933530 < baseStart_4933530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933533 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_4933533 : Nat := 118140960795 + 4933533 * 2 ^ 59
def prefixEnd_4933533 : Nat := 4983230072969 + 3 ^ 40 * 4933533 * 2
def baseEnd_4933533 : Nat := 2533273753818151263148601

theorem tailTrace_4933533 : CollatzResearch.WordTrace tailWord_4933533 prefixEnd_4933533 2533273753818151263148601 := by
  unfold tailWord_4933533
  simp only [CollatzResearch.WordTrace]
  refine ⟨179940731235659996200261253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119960487490439997466840835 179940731235659996200261253)
  ·
    refine ⟨33738887106686249287548985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179940731235659996200261253 33738887106686249287548985)
    ·
      refine ⟨25304165330014686965661739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33738887106686249287548985 25304165330014686965661739)
      ·
        refine ⟨37956247995022030448492609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25304165330014686965661739 37956247995022030448492609)
        ·
          refine ⟨28467185996266522836369457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37956247995022030448492609 28467185996266522836369457)
          ·
            refine ⟨21350389497199892127277093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28467185996266522836369457 21350389497199892127277093)
            ·
              refine ⟨4003198030724979773864455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21350389497199892127277093 4003198030724979773864455)
              ·
                refine ⟨6004797046087469660796683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003198030724979773864455 6004797046087469660796683)
                ·
                  refine ⟨9007195569131204491195025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6004797046087469660796683 9007195569131204491195025)
                  ·
                    refine ⟨6755396676848403368396269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9007195569131204491195025 6755396676848403368396269)
                    ·
                      refine ⟨2533273753818151263148601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755396676848403368396269 2533273753818151263148601)
                      ·
                        rfl

theorem cell23_4933533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_4933533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933533 prefixEnd_4933533 := by exact prefixLift 4933533
  have htrace : WordTrace (prefixWord ++ tailWord_4933533) baseStart_4933533 baseEnd_4933533 := by
    simpa [prefixWord, tailWord_4933533, baseEnd_4933533] using wordTrace_append hprefix tailTrace_4933533
  have hstable : (prefixWord ++ tailWord_4933533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933533).length < 2 ^ (prefixWord ++ tailWord_4933533).sum := by decide
  have hdescent : baseEnd_4933533 < baseStart_4933533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933550 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4933550 : Nat := 118140960795 + 4933550 * 2 ^ 59
def prefixEnd_4933550 : Nat := 4983230072969 + 3 ^ 40 * 4933550 * 2
def baseEnd_4933550 : Nat := 2533282482989277696636023

theorem tailTrace_4933550 : CollatzResearch.WordTrace tailWord_4933550 prefixEnd_4933550 2533282482989277696636023 := by
  unfold tailWord_4933550
  simp only [CollatzResearch.WordTrace]
  refine ⟨22492668909574801012953763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119960900851065605402420069 22492668909574801012953763)
  ·
    refine ⟨33739003364362201519430645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22492668909574801012953763 33739003364362201519430645)
    ·
      refine ⟨3163031565408956392446623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33739003364362201519430645 3163031565408956392446623)
      ·
        refine ⟨4744547348113434588669935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3163031565408956392446623 4744547348113434588669935)
        ·
          refine ⟨7116821022170151883004903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744547348113434588669935 7116821022170151883004903)
          ·
            refine ⟨10675231533255227824507355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7116821022170151883004903 10675231533255227824507355)
            ·
              refine ⟨16012847299882841736761033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10675231533255227824507355 16012847299882841736761033)
              ·
                refine ⟨12009635474912131302570775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16012847299882841736761033 12009635474912131302570775)
                ·
                  refine ⟨18014453212368196953856163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12009635474912131302570775 18014453212368196953856163)
                  ·
                    refine ⟨27021679818552295430784245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18014453212368196953856163 27021679818552295430784245)
                    ·
                      refine ⟨2533282482989277696636023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27021679818552295430784245 2533282482989277696636023)
                      ·
                        rfl

theorem cell23_4933550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4933550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933550 prefixEnd_4933550 := by exact prefixLift 4933550
  have htrace : WordTrace (prefixWord ++ tailWord_4933550) baseStart_4933550 baseEnd_4933550 := by
    simpa [prefixWord, tailWord_4933550, baseEnd_4933550] using wordTrace_append hprefix tailTrace_4933550
  have hstable : (prefixWord ++ tailWord_4933550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933550).length < 2 ^ (prefixWord ++ tailWord_4933550).sum := by decide
  have hdescent : baseEnd_4933550 < baseStart_4933550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933562 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_4933562 : Nat := 118140960795 + 4933562 * 2 ^ 59
def prefixEnd_4933562 : Nat := 4983230072969 + 3 ^ 40 * 4933562 * 2
def baseEnd_4933562 : Nat := 844429548252377216561989

theorem tailTrace_4933562 : CollatzResearch.WordTrace tailWord_4933562 prefixEnd_4933562 844429548252377216561989 := by
  unfold tailWord_4933562
  simp only [CollatzResearch.WordTrace]
  refine ⟨44985447238138733538266735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119961192635036622768711293 44985447238138733538266735)
  ·
    refine ⟨67478170857208100307400103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44985447238138733538266735 67478170857208100307400103)
    ·
      refine ⟨101217256285812150461100155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67478170857208100307400103 101217256285812150461100155)
      ·
        refine ⟨151825884428718225691650233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101217256285812150461100155 151825884428718225691650233)
        ·
          refine ⟨113869413321538669268737675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151825884428718225691650233 113869413321538669268737675)
          ·
            refine ⟨170804119982308003903106513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113869413321538669268737675 170804119982308003903106513)
            ·
              refine ⟨128103089986731002927329885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170804119982308003903106513 128103089986731002927329885)
              ·
                refine ⟨48038658745024126097748707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128103089986731002927329885 48038658745024126097748707)
                ·
                  refine ⟨72057988117536189146623061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48038658745024126097748707 72057988117536189146623061)
                  ·
                    refine ⟨844429548252377216561989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72057988117536189146623061 844429548252377216561989)
                    ·
                      rfl

theorem cell23_4933562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_4933562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933562 prefixEnd_4933562 := by exact prefixLift 4933562
  have htrace : WordTrace (prefixWord ++ tailWord_4933562) baseStart_4933562 baseEnd_4933562 := by
    simpa [prefixWord, tailWord_4933562, baseEnd_4933562] using wordTrace_append hprefix tailTrace_4933562
  have hstable : (prefixWord ++ tailWord_4933562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933562).length < 2 ^ (prefixWord ++ tailWord_4933562).sum := by decide
  have hdescent : baseEnd_4933562 < baseStart_4933562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933589 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4933589 : Nat := 118140960795 + 4933589 * 2 ^ 59
def prefixEnd_4933589 : Nat := 4983230072969 + 3 ^ 40 * 4933589 * 2
def baseEnd_4933589 : Nat := 2533302508734803044048343

theorem tailTrace_4933589 : CollatzResearch.WordTrace tailWord_4933589 prefixEnd_4933589 2533302508734803044048343 := by
  unfold tailWord_4933589
  simp only [CollatzResearch.WordTrace]
  refine ⟨179942773723457117764299821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119961849148971411842866547 179942773723457117764299821)
  ·
    refine ⟨67478540146296419161612433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179942773723457117764299821 67478540146296419161612433)
    ·
      refine ⟨50608905109722314371209325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67478540146296419161612433 50608905109722314371209325)
      ·
        refine ⟨18978339416145867889203497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50608905109722314371209325 18978339416145867889203497)
        ·
          refine ⟨14233754562109400916902623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18978339416145867889203497 14233754562109400916902623)
          ·
            refine ⟨21350631843164101375353935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14233754562109400916902623 21350631843164101375353935)
            ·
              refine ⟨32025947764746152063030903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21350631843164101375353935 32025947764746152063030903)
              ·
                refine ⟨48038921647119228094546355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32025947764746152063030903 48038921647119228094546355)
                ·
                  refine ⟨72058382470678842141819533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48038921647119228094546355 72058382470678842141819533)
                  ·
                    refine ⟨27021893426504565803182325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72058382470678842141819533 27021893426504565803182325)
                    ·
                      refine ⟨2533302508734803044048343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27021893426504565803182325 2533302508734803044048343)
                      ·
                        rfl

theorem cell23_4933589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4933589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933589 prefixEnd_4933589 := by exact prefixLift 4933589
  have htrace : WordTrace (prefixWord ++ tailWord_4933589) baseStart_4933589 baseEnd_4933589 := by
    simpa [prefixWord, tailWord_4933589, baseEnd_4933589] using wordTrace_append hprefix tailTrace_4933589
  have hstable : (prefixWord ++ tailWord_4933589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933589).length < 2 ^ (prefixWord ++ tailWord_4933589).sum := by decide
  have hdescent : baseEnd_4933589 < baseStart_4933589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933603 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4933603 : Nat := 118140960795 + 4933603 * 2 ^ 59
def prefixEnd_4933603 : Nat := 4983230072969 + 3 ^ 40 * 4933603 * 2
def baseEnd_4933603 : Nat := 2533309697463965989273279

theorem tailTrace_4933603 : CollatzResearch.WordTrace tailWord_4933603 prefixEnd_4933603 2533309697463965989273279 := by
  unfold tailWord_4933603
  simp only [CollatzResearch.WordTrace]
  refine ⟨179943284345406398155309463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119962189563604265436872975 179943284345406398155309463)
  ·
    refine ⟨269914926518109597232964195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179943284345406398155309463 269914926518109597232964195)
    ·
      refine ⟨404872389777164395849446293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269914926518109597232964195 404872389777164395849446293)
      ·
        refine ⟨18978393270804581055442795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 404872389777164395849446293 18978393270804581055442795)
        ·
          refine ⟨28467589906206871583164193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18978393270804581055442795 28467589906206871583164193)
          ·
            refine ⟨21350692429655153687373145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28467589906206871583164193 21350692429655153687373145)
            ·
              refine ⟨16013019322241365265529859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21350692429655153687373145 16013019322241365265529859)
              ·
                refine ⟨24019528983362047898294789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16013019322241365265529859 24019528983362047898294789)
                ·
                  refine ⟨4503661684380383980930273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24019528983362047898294789 4503661684380383980930273)
                  ·
                    refine ⟨3377746263285287985697705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4503661684380383980930273 3377746263285287985697705)
                    ·
                      refine ⟨2533309697463965989273279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377746263285287985697705 2533309697463965989273279)
                      ·
                        rfl

theorem cell23_4933603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4933603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933603 prefixEnd_4933603 := by exact prefixLift 4933603
  have htrace : WordTrace (prefixWord ++ tailWord_4933603) baseStart_4933603 baseEnd_4933603 := by
    simpa [prefixWord, tailWord_4933603, baseEnd_4933603] using wordTrace_append hprefix tailTrace_4933603
  have hstable : (prefixWord ++ tailWord_4933603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933603).length < 2 ^ (prefixWord ++ tailWord_4933603).sum := by decide
  have hdescent : baseEnd_4933603 < baseStart_4933603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933619 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3]
def baseStart_4933619 : Nat := 118140960795 + 4933619 * 2 ^ 59
def prefixEnd_4933619 : Nat := 4983230072969 + 3 ^ 40 * 4933619 * 2
def baseEnd_4933619 : Nat := 2533317913154437926673205

theorem tailTrace_4933619 : CollatzResearch.WordTrace tailWord_4933619 prefixEnd_4933619 2533317913154437926673205 := by
  unfold tailWord_4933619
  simp only [CollatzResearch.WordTrace]
  refine ⟨179943867913348432887891911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119962578608898955258594607 179943867913348432887891911)
  ·
    refine ⟨269915801870022649331837867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179943867913348432887891911 269915801870022649331837867)
    ·
      refine ⟨404873702805033973997756801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269915801870022649331837867 404873702805033973997756801)
      ·
        refine ⟨303655277103775480498317601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404873702805033973997756801 303655277103775480498317601)
        ·
          refine ⟨227741457827831610373738201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303655277103775480498317601 227741457827831610373738201)
          ·
            refine ⟨170806093370873707780303651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227741457827831610373738201 170806093370873707780303651)
            ·
              refine ⟨256209140056310561670455477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170806093370873707780303651 256209140056310561670455477)
              ·
                refine ⟨24019606880279115156605201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 256209140056310561670455477 24019606880279115156605201)
                ·
                  refine ⟨18014705160209336367453901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24019606880279115156605201 18014705160209336367453901)
                  ·
                    refine ⟨6755514435078501137795213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18014705160209336367453901 6755514435078501137795213)
                    ·
                      refine ⟨2533317913154437926673205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755514435078501137795213 2533317913154437926673205)
                      ·
                        rfl

theorem cell23_4933619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_4933619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933619 prefixEnd_4933619 := by exact prefixLift 4933619
  have htrace : WordTrace (prefixWord ++ tailWord_4933619) baseStart_4933619 baseEnd_4933619 := by
    simpa [prefixWord, tailWord_4933619, baseEnd_4933619] using wordTrace_append hprefix tailTrace_4933619
  have hstable : (prefixWord ++ tailWord_4933619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933619).length < 2 ^ (prefixWord ++ tailWord_4933619).sum := by decide
  have hdescent : baseEnd_4933619 < baseStart_4933619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933659 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4]
def baseStart_4933659 : Nat := 118140960795 + 4933659 * 2 ^ 59
def prefixEnd_4933659 : Nat := 4983230072969 + 3 ^ 40 * 4933659 * 2
def baseEnd_4933659 : Nat := 2533338452380617770173021

theorem tailTrace_4933659 : CollatzResearch.WordTrace tailWord_4933659 prefixEnd_4933659 2533338452380617770173021 := by
  unfold tailWord_4933659
  simp only [CollatzResearch.WordTrace]
  refine ⟨179945326833203519719348031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119963551222135679812898687 179945326833203519719348031)
  ·
    refine ⟨269917990249805279579022047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179945326833203519719348031 269917990249805279579022047)
    ·
      refine ⟨404876985374707919368533071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269917990249805279579022047 404876985374707919368533071)
      ·
        refine ⟨607315478062061879052799607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404876985374707919368533071 607315478062061879052799607)
        ·
          refine ⟨910973217093092818579199411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607315478062061879052799607 910973217093092818579199411)
          ·
            refine ⟨1366459825639639227868799117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 910973217093092818579199411 1366459825639639227868799117)
            ·
              refine ⟨512422434614864710450799669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1366459825639639227868799117 512422434614864710450799669)
              ·
                refine ⟨48039603245143566604762469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512422434614864710450799669 48039603245143566604762469)
                ·
                  refine ⟨9007425608464418738392963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48039603245143566604762469 9007425608464418738392963)
                  ·
                    refine ⟨13511138412696628107589445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9007425608464418738392963 13511138412696628107589445)
                    ·
                      refine ⟨2533338452380617770173021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13511138412696628107589445 2533338452380617770173021)
                      ·
                        rfl

theorem cell23_4933659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4].length) (baseStart_4933659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933659 prefixEnd_4933659 := by exact prefixLift 4933659
  have htrace : WordTrace (prefixWord ++ tailWord_4933659) baseStart_4933659 baseEnd_4933659 := by
    simpa [prefixWord, tailWord_4933659, baseEnd_4933659] using wordTrace_append hprefix tailTrace_4933659
  have hstable : (prefixWord ++ tailWord_4933659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933659).length < 2 ^ (prefixWord ++ tailWord_4933659).sum := by decide
  have hdescent : baseEnd_4933659 < baseStart_4933659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933660 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 5]
def baseStart_4933660 : Nat := 118140960795 + 4933660 * 2 ^ 59
def prefixEnd_4933660 : Nat := 4983230072969 + 3 ^ 40 * 4933660 * 2
def baseEnd_4933660 : Nat := 281482107317919140695613

theorem tailTrace_4933660 : CollatzResearch.WordTrace tailWord_4933660 prefixEnd_4933660 281482107317919140695613 := by
  unfold tailWord_4933660
  simp only [CollatzResearch.WordTrace]
  refine ⟨89972681653099948445067217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119963575537466597926756289 89972681653099948445067217)
  ·
    refine ⟨67479511239824961333800413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89972681653099948445067217 67479511239824961333800413)
    ·
      refine ⟨25304816714934360500175155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67479511239824961333800413 25304816714934360500175155)
      ·
        refine ⟨37957225072401540750262733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25304816714934360500175155 37957225072401540750262733)
        ·
          refine ⟨14233959402150577781348525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37957225072401540750262733 14233959402150577781348525)
          ·
            refine ⟨5337734775806466668005697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14233959402150577781348525 5337734775806466668005697)
            ·
              refine ⟨4003301081854850001004273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5337734775806466668005697 4003301081854850001004273)
              ·
                refine ⟨3002475811391137500753205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003301081854850001004273 3002475811391137500753205)
                ·
                  refine ⟨281482107317919140695613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002475811391137500753205 281482107317919140695613)
                  ·
                    rfl

theorem cell23_4933660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_4933660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933660 prefixEnd_4933660 := by exact prefixLift 4933660
  have htrace : WordTrace (prefixWord ++ tailWord_4933660) baseStart_4933660 baseEnd_4933660 := by
    simpa [prefixWord, tailWord_4933660, baseEnd_4933660] using wordTrace_append hprefix tailTrace_4933660
  have hstable : (prefixWord ++ tailWord_4933660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933660).length < 2 ^ (prefixWord ++ tailWord_4933660).sum := by decide
  have hdescent : baseEnd_4933660 < baseStart_4933660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933696 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_4933696 : Nat := 118140960795 + 4933696 * 2 ^ 59
def prefixEnd_4933696 : Nat := 4983230072969 + 3 ^ 40 * 4933696 * 2
def baseEnd_4933696 : Nat := 2533357451164834125410351

theorem tailTrace_4933696 : CollatzResearch.WordTrace tailWord_4933696 prefixEnd_4933696 2533357451164834125410351 := by
  unfold tailWord_4933696
  simp only [CollatzResearch.WordTrace]
  refine ⟨89973338167034737519222471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119964450889379650025629961 89973338167034737519222471)
  ·
    refine ⟨134960007250552106278833707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89973338167034737519222471 134960007250552106278833707)
    ·
      refine ⟨202440010875828159418250561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134960007250552106278833707 202440010875828159418250561)
      ·
        refine ⟨151830008156871119563687921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202440010875828159418250561 151830008156871119563687921)
        ·
          refine ⟨113872506117653339672765941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151830008156871119563687921 113872506117653339672765941)
          ·
            refine ⟨10675547448530000594321807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113872506117653339672765941 10675547448530000594321807)
            ·
              refine ⟨16013321172795000891482711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10675547448530000594321807 16013321172795000891482711)
              ·
                refine ⟨24019981759192501337224067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16013321172795000891482711 24019981759192501337224067)
                ·
                  refine ⟨36029972638788752005836101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24019981759192501337224067 36029972638788752005836101)
                  ·
                    refine ⟨6755619869772891001094269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36029972638788752005836101 6755619869772891001094269)
                    ·
                      refine ⟨2533357451164834125410351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755619869772891001094269 2533357451164834125410351)
                      ·
                        rfl

theorem cell23_4933696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_4933696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933696 prefixEnd_4933696 := by exact prefixLift 4933696
  have htrace : WordTrace (prefixWord ++ tailWord_4933696) baseStart_4933696 baseEnd_4933696 := by
    simpa [prefixWord, tailWord_4933696, baseEnd_4933696] using wordTrace_append hprefix tailTrace_4933696
  have hstable : (prefixWord ++ tailWord_4933696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933696).length < 2 ^ (prefixWord ++ tailWord_4933696).sum := by decide
  have hdescent : baseEnd_4933696 < baseStart_4933696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933719 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_4933719 : Nat := 118140960795 + 4933719 * 2 ^ 59
def prefixEnd_4933719 : Nat := 4983230072969 + 3 ^ 40 * 4933719 * 2
def baseEnd_4933719 : Nat := 2533369261219887535422745

theorem tailTrace_4933719 : CollatzResearch.WordTrace tailWord_4933719 prefixEnd_4933719 2533369261219887535422745 := by
  unfold tailWord_4933719
  simp only [CollatzResearch.WordTrace]
  refine ⟨179947515212986149966532211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119965010141990766644354807 179947515212986149966532211)
  ·
    refine ⟨269921272819479224949798317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179947515212986149966532211 269921272819479224949798317)
    ·
      refine ⟨101220477307304709356174369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269921272819479224949798317 101220477307304709356174369)
      ·
        refine ⟨75915357980478532017130777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101220477307304709356174369 75915357980478532017130777)
        ·
          refine ⟨56936518485358899012848083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75915357980478532017130777 56936518485358899012848083)
          ·
            refine ⟨85404777728038348519272125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56936518485358899012848083 85404777728038348519272125)
            ·
              refine ⟨32026791648014380694727047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85404777728038348519272125 32026791648014380694727047)
              ·
                refine ⟨48040187472021571042090571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32026791648014380694727047 48040187472021571042090571)
                ·
                  refine ⟨72060281208032356563135857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48040187472021571042090571 72060281208032356563135857)
                  ·
                    refine ⟨54045210906024267422351893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72060281208032356563135857 54045210906024267422351893)
                    ·
                      refine ⟨2533369261219887535422745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54045210906024267422351893 2533369261219887535422745)
                      ·
                        rfl

theorem cell23_4933719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_4933719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933719 prefixEnd_4933719 := by exact prefixLift 4933719
  have htrace : WordTrace (prefixWord ++ tailWord_4933719) baseStart_4933719 baseEnd_4933719 := by
    simpa [prefixWord, tailWord_4933719, baseEnd_4933719] using wordTrace_append hprefix tailTrace_4933719
  have hstable : (prefixWord ++ tailWord_4933719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933719).length < 2 ^ (prefixWord ++ tailWord_4933719).sum := by decide
  have hdescent : baseEnd_4933719 < baseStart_4933719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933733 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 6]
def baseStart_4933733 : Nat := 118140960795 + 4933733 * 2 ^ 59
def prefixEnd_4933733 : Nat := 4983230072969 + 3 ^ 40 * 4933733 * 2
def baseEnd_4933733 : Nat := 281486272216561164516409

theorem tailTrace_4933733 : CollatzResearch.WordTrace tailWord_4933733 prefixEnd_4933733 281486272216561164516409 := by
  unfold tailWord_4933733
  simp only [CollatzResearch.WordTrace]
  refine ⟨179948025834935430357541853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119965350556623620238361235 179948025834935430357541853)
  ·
    refine ⟨67480509688100786384078195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179948025834935430357541853 67480509688100786384078195)
    ·
      refine ⟨101220764532151179576117293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67480509688100786384078195 101220764532151179576117293)
      ·
        refine ⟨37957786699556692341043985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101220764532151179576117293 37957786699556692341043985)
        ·
          refine ⟨28468340024667519255782989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37957786699556692341043985 28468340024667519255782989)
          ·
            refine ⟨10675627509250319720918621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28468340024667519255782989 10675627509250319720918621)
            ·
              refine ⟨4003360315968869895344483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10675627509250319720918621 4003360315968869895344483)
              ·
                refine ⟨6005040473953304843016725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003360315968869895344483 6005040473953304843016725)
                ·
                  refine ⟨281486272216561164516409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6005040473953304843016725 281486272216561164516409)
                  ·
                    rfl

theorem cell23_4933733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_4933733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933733 prefixEnd_4933733 := by exact prefixLift 4933733
  have htrace : WordTrace (prefixWord ++ tailWord_4933733) baseStart_4933733 baseEnd_4933733 := by
    simpa [prefixWord, tailWord_4933733, baseEnd_4933733] using wordTrace_append hprefix tailTrace_4933733
  have hstable : (prefixWord ++ tailWord_4933733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933733).length < 2 ^ (prefixWord ++ tailWord_4933733).sum := by decide
  have hdescent : baseEnd_4933733 < baseStart_4933733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933743 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 3]
def baseStart_4933743 : Nat := 118140960795 + 4933743 * 2 ^ 59
def prefixEnd_4933743 : Nat := 4983230072969 + 3 ^ 40 * 4933743 * 2
def baseEnd_4933743 : Nat := 2533381584755595441522635

theorem tailTrace_4933743 : CollatzResearch.WordTrace tailWord_4933743 prefixEnd_4933743 2533381584755595441522635 := by
  unfold tailWord_4933743
  simp only [CollatzResearch.WordTrace]
  refine ⟨179948390564899202065405883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119965593709932801376937255 179948390564899202065405883)
  ·
    refine ⟨269922585847348803098108825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179948390564899202065405883 269922585847348803098108825)
    ·
      refine ⟨202441939385511602323581619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269922585847348803098108825 202441939385511602323581619)
      ·
        refine ⟨303662909078267403485372429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202441939385511602323581619 303662909078267403485372429)
        ·
          refine ⟨113873590904350276307014661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303662909078267403485372429 113873590904350276307014661)
          ·
            refine ⟨21351298294565676807565249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113873590904350276307014661 21351298294565676807565249)
            ·
              refine ⟨16013473720924257605673937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21351298294565676807565249 16013473720924257605673937)
              ·
                refine ⟨12010105290693193204255453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16013473720924257605673937 12010105290693193204255453)
                ·
                  refine ⟨4503789484009947451595795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12010105290693193204255453 4503789484009947451595795)
                  ·
                    refine ⟨6755684226014921177393693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503789484009947451595795 6755684226014921177393693)
                    ·
                      refine ⟨2533381584755595441522635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755684226014921177393693 2533381584755595441522635)
                      ·
                        rfl

theorem cell23_4933743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_4933743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933743 prefixEnd_4933743 := by exact prefixLift 4933743
  have htrace : WordTrace (prefixWord ++ tailWord_4933743) baseStart_4933743 baseEnd_4933743 := by
    simpa [prefixWord, tailWord_4933743, baseEnd_4933743] using wordTrace_append hprefix tailTrace_4933743
  have hstable : (prefixWord ++ tailWord_4933743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933743).length < 2 ^ (prefixWord ++ tailWord_4933743).sum := by decide
  have hdescent : baseEnd_4933743 < baseStart_4933743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933753 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 5, 2]
def baseStart_4933753 : Nat := 118140960795 + 4933753 * 2 ^ 59
def prefixEnd_4933753 : Nat := 4983230072969 + 3 ^ 40 * 4933753 * 2
def baseEnd_4933753 : Nat := 2533386719562140402397589

theorem tailTrace_4933753 : CollatzResearch.WordTrace tailWord_4933753 prefixEnd_4933753 2533386719562140402397589 := by
  unfold tailWord_4933753
  simp only [CollatzResearch.WordTrace]
  refine ⟨179948755294862973773269913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119965836863241982515513275 179948755294862973773269913)
  ·
    refine ⟨134961566471147230329952435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179948755294862973773269913 134961566471147230329952435)
    ·
      refine ⟨202442349706720845494928653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134961566471147230329952435 202442349706720845494928653)
      ·
        refine ⟨75915881140020317060598245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202442349706720845494928653 75915881140020317060598245)
        ·
          refine ⟨14234227713753809448862171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75915881140020317060598245 14234227713753809448862171)
          ·
            refine ⟨21351341570630714173293257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14234227713753809448862171 21351341570630714173293257)
            ·
              refine ⟨16013506177973035629969943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21351341570630714173293257 16013506177973035629969943)
              ·
                refine ⟨24020259266959553444954915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16013506177973035629969943 24020259266959553444954915)
                ·
                  refine ⟨36030388900439330167432373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24020259266959553444954915 36030388900439330167432373)
                  ·
                    refine ⟨3377848959416187203196785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36030388900439330167432373 3377848959416187203196785)
                    ·
                      refine ⟨2533386719562140402397589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377848959416187203196785 2533386719562140402397589)
                      ·
                        rfl

theorem cell23_4933753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_4933753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933753 prefixEnd_4933753 := by exact prefixLift 4933753
  have htrace : WordTrace (prefixWord ++ tailWord_4933753) baseStart_4933753 baseEnd_4933753 := by
    simpa [prefixWord, tailWord_4933753, baseEnd_4933753] using wordTrace_append hprefix tailTrace_4933753
  have hstable : (prefixWord ++ tailWord_4933753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933753).length < 2 ^ (prefixWord ++ tailWord_4933753).sum := by decide
  have hdescent : baseEnd_4933753 < baseStart_4933753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933770 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_4933770 : Nat := 118140960795 + 4933770 * 2 ^ 59
def prefixEnd_4933770 : Nat := 4983230072969 + 3 ^ 40 * 4933770 * 2
def baseEnd_4933770 : Nat := 2533395448733266835885011

theorem tailTrace_4933770 : CollatzResearch.WordTrace tailWord_4933770 prefixEnd_4933770 2533395448733266835885011 := by
  unfold tailWord_4933770
  simp only [CollatzResearch.WordTrace]
  refine ⟨44987343833950346419159691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119966250223867590451092509 44987343833950346419159691)
  ·
    refine ⟨67481015750925519628739537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44987343833950346419159691 67481015750925519628739537)
    ·
      refine ⟨50610761813194139721554653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67481015750925519628739537 50610761813194139721554653)
      ·
        refine ⟨18979035679947802395582995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50610761813194139721554653 18979035679947802395582995)
        ·
          refine ⟨28468553519921703593374493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18979035679947802395582995 28468553519921703593374493)
          ·
            refine ⟨10675707569970638847515435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28468553519921703593374493 10675707569970638847515435)
            ·
              refine ⟨16013561354955958271273153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10675707569970638847515435 16013561354955958271273153)
              ·
                refine ⟨12010171016216968703454865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16013561354955958271273153 12010171016216968703454865)
                ·
                  refine ⟨9007628262162726527591149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12010171016216968703454865 9007628262162726527591149)
                  ·
                    refine ⟨3377860598311022447846681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9007628262162726527591149 3377860598311022447846681)
                    ·
                      refine ⟨2533395448733266835885011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377860598311022447846681 2533395448733266835885011)
                      ·
                        rfl

theorem cell23_4933770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_4933770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933770 prefixEnd_4933770 := by exact prefixLift 4933770
  have htrace : WordTrace (prefixWord ++ tailWord_4933770) baseStart_4933770 baseEnd_4933770 := by
    simpa [prefixWord, tailWord_4933770, baseEnd_4933770] using wordTrace_append hprefix tailTrace_4933770
  have hstable : (prefixWord ++ tailWord_4933770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933770).length < 2 ^ (prefixWord ++ tailWord_4933770).sum := by decide
  have hdescent : baseEnd_4933770 < baseStart_4933770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933776 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_4933776 : Nat := 118140960795 + 4933776 * 2 ^ 59
def prefixEnd_4933776 : Nat := 4983230072969 + 3 ^ 40 * 4933776 * 2
def baseEnd_4933776 : Nat := 844466176539064604136661

theorem tailTrace_4933776 : CollatzResearch.WordTrace tailWord_4933776 prefixEnd_4933776 844466176539064604136661 := by
  unfold tailWord_4933776
  simp only [CollatzResearch.WordTrace]
  refine ⟨89974797086889824350678591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119966396115853099134238121 89974797086889824350678591)
  ·
    refine ⟨134962195630334736526017887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89974797086889824350678591 134962195630334736526017887)
    ·
      refine ⟨202443293445502104789026831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134962195630334736526017887 202443293445502104789026831)
      ·
        refine ⟨303664940168253157183540247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202443293445502104789026831 303664940168253157183540247)
        ·
          refine ⟨455497410252379735775310371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303664940168253157183540247 455497410252379735775310371)
          ·
            refine ⟨683246115378569603662965557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455497410252379735775310371 683246115378569603662965557)
            ·
              refine ⟨64054323316740900343403021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 683246115378569603662965557 64054323316740900343403021)
              ·
                refine ⟨24020371243777837628776133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64054323316740900343403021 24020371243777837628776133)
                ·
                  refine ⟨4503819608208344555395525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24020371243777837628776133 4503819608208344555395525)
                  ·
                    refine ⟨844466176539064604136661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4503819608208344555395525 844466176539064604136661)
                    ·
                      rfl

theorem cell23_4933776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_4933776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933776 prefixEnd_4933776 := by exact prefixLift 4933776
  have htrace : WordTrace (prefixWord ++ tailWord_4933776) baseStart_4933776 baseEnd_4933776 := by
    simpa [prefixWord, tailWord_4933776, baseEnd_4933776] using wordTrace_append hprefix tailTrace_4933776
  have hstable : (prefixWord ++ tailWord_4933776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933776).length < 2 ^ (prefixWord ++ tailWord_4933776).sum := by decide
  have hdescent : baseEnd_4933776 < baseStart_4933776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933817 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 1, 2, 2]
def baseStart_4933817 : Nat := 118140960795 + 4933817 * 2 ^ 59
def prefixEnd_4933817 : Nat := 4983230072969 + 3 ^ 40 * 4933817 * 2
def baseEnd_4933817 : Nat := 2533419582324028151997295

theorem tailTrace_4933817 : CollatzResearch.WordTrace tailWord_4933817 prefixEnd_4933817 2533419582324028151997295 := by
  unfold tailWord_4933817
  simp only [CollatzResearch.WordTrace]
  refine ⟨179951089566631112703599705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119967393044420741802399803 179951089566631112703599705)
  ·
    refine ⟨134963317174973334527699779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179951089566631112703599705 134963317174973334527699779)
    ·
      refine ⟨202444975762460001791549669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134963317174973334527699779 202444975762460001791549669)
      ·
        refine ⟨37958432955461250335915563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202444975762460001791549669 37958432955461250335915563)
        ·
          refine ⟨56937649433191875503873345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37958432955461250335915563 56937649433191875503873345)
          ·
            refine ⟨42703237074893906627905009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56937649433191875503873345 42703237074893906627905009)
            ·
              refine ⟨32027427806170429970928757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42703237074893906627905009 32027427806170429970928757)
              ·
                refine ⟨3002571356828477809774571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32027427806170429970928757 3002571356828477809774571)
                ·
                  refine ⟨4503857035242716714661857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002571356828477809774571 4503857035242716714661857)
                  ·
                    refine ⟨3377892776432037535996393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4503857035242716714661857 3377892776432037535996393)
                    ·
                      refine ⟨2533419582324028151997295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377892776432037535996393 2533419582324028151997295)
                      ·
                        rfl

theorem cell23_4933817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_4933817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933817 prefixEnd_4933817 := by exact prefixLift 4933817
  have htrace : WordTrace (prefixWord ++ tailWord_4933817) baseStart_4933817 baseEnd_4933817 := by
    simpa [prefixWord, tailWord_4933817, baseEnd_4933817] using wordTrace_append hprefix tailTrace_4933817
  have hstable : (prefixWord ++ tailWord_4933817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933817).length < 2 ^ (prefixWord ++ tailWord_4933817).sum := by decide
  have hdescent : baseEnd_4933817 < baseStart_4933817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933820 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4933820 : Nat := 118140960795 + 4933820 * 2 ^ 59
def prefixEnd_4933820 : Nat := 4983230072969 + 3 ^ 40 * 4933820 * 2
def baseEnd_4933820 : Nat := 2533421122765991640259781

theorem tailTrace_4933820 : CollatzResearch.WordTrace tailWord_4933820 prefixEnd_4933820 2533421122765991640259781 := by
  unfold tailWord_4933820
  simp only [CollatzResearch.WordTrace]
  refine ⟨89975599492810122107979457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119967465990413496143972609 89975599492810122107979457)
  ·
    refine ⟨67481699619607591580984593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89975599492810122107979457 67481699619607591580984593)
    ·
      refine ⟨50611274714705693685738445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67481699619607591580984593 50611274714705693685738445)
      ·
        refine ⟨18979228018014635132151917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50611274714705693685738445 18979228018014635132151917)
        ·
          refine ⟨7117210506755488174556969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18979228018014635132151917 7117210506755488174556969)
          ·
            refine ⟨5337907880066616130917727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7117210506755488174556969 5337907880066616130917727)
            ·
              refine ⟨8006861820099924196376591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337907880066616130917727 8006861820099924196376591)
              ·
                refine ⟨12010292730149886294564887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8006861820099924196376591 12010292730149886294564887)
                ·
                  refine ⟨18015439095224829441847331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12010292730149886294564887 18015439095224829441847331)
                  ·
                    refine ⟨27023158642837244162770997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18015439095224829441847331 27023158642837244162770997)
                    ·
                      refine ⟨2533421122765991640259781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27023158642837244162770997 2533421122765991640259781)
                      ·
                        rfl

theorem cell23_4933820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4933820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933820 prefixEnd_4933820 := by exact prefixLift 4933820
  have htrace : WordTrace (prefixWord ++ tailWord_4933820) baseStart_4933820 baseEnd_4933820 := by
    simpa [prefixWord, tailWord_4933820, baseEnd_4933820] using wordTrace_append hprefix tailTrace_4933820
  have hstable : (prefixWord ++ tailWord_4933820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933820).length < 2 ^ (prefixWord ++ tailWord_4933820).sum := by decide
  have hdescent : baseEnd_4933820 < baseStart_4933820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933850 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_4933850 : Nat := 118140960795 + 4933850 * 2 ^ 59
def prefixEnd_4933850 : Nat := 4983230072969 + 3 ^ 40 * 4933850 * 2
def baseEnd_4933850 : Nat := 2533436527185626522884643

theorem tailTrace_4933850 : CollatzResearch.WordTrace tailWord_4933850 prefixEnd_4933850 2533436527185626522884643 := by
  unfold tailWord_4933850
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988073293877889834887751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119968195450341039559700669 44988073293877889834887751)
  ·
    refine ⟨67482109940816834752331627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44988073293877889834887751 67482109940816834752331627)
    ·
      refine ⟨101223164911225252128497441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67482109940816834752331627 101223164911225252128497441)
      ·
        refine ⟨75917373683418939096373081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101223164911225252128497441 75917373683418939096373081)
        ·
          refine ⟨56938030262564204322279811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75917373683418939096373081 56938030262564204322279811)
          ·
            refine ⟨85407045393846306483419717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56938030262564204322279811 85407045393846306483419717)
            ·
              refine ⟨16013821011346182465641197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85407045393846306483419717 16013821011346182465641197)
              ·
                refine ⟨6005182879254818424615449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16013821011346182465641197 6005182879254818424615449)
                ·
                  refine ⟨4503887159441113818461587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005182879254818424615449 4503887159441113818461587)
                  ·
                    refine ⟨6755830739161670727692381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4503887159441113818461587 6755830739161670727692381)
                    ·
                      refine ⟨2533436527185626522884643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6755830739161670727692381 2533436527185626522884643)
                      ·
                        rfl

theorem cell23_4933850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_4933850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933850 prefixEnd_4933850 := by exact prefixLift 4933850
  have htrace : WordTrace (prefixWord ++ tailWord_4933850) baseStart_4933850 baseEnd_4933850 := by
    simpa [prefixWord, tailWord_4933850, baseEnd_4933850] using wordTrace_append hprefix tailTrace_4933850
  have hstable : (prefixWord ++ tailWord_4933850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933850).length < 2 ^ (prefixWord ++ tailWord_4933850).sum := by decide
  have hdescent : baseEnd_4933850 < baseStart_4933850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933856 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_4933856 : Nat := 118140960795 + 4933856 * 2 ^ 59
def prefixEnd_4933856 : Nat := 4983230072969 + 3 ^ 40 * 4933856 * 2
def baseEnd_4933856 : Nat := 2533439608069553499409615

theorem tailTrace_4933856 : CollatzResearch.WordTrace tailWord_4933856 prefixEnd_4933856 2533439608069553499409615 := by
  unfold tailWord_4933856
  simp only [CollatzResearch.WordTrace]
  refine ⟨89976256006744911182134711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119968341342326548242846281 89976256006744911182134711)
  ·
    refine ⟨134964384010117366773202067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89976256006744911182134711 134964384010117366773202067)
    ·
      refine ⟨202446576015176050159803101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134964384010117366773202067 202446576015176050159803101)
      ·
        refine ⟨75917466005691018809926163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202446576015176050159803101 75917466005691018809926163)
        ·
          refine ⟨113876199008536528214889245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75917466005691018809926163 113876199008536528214889245)
          ·
            refine ⟨42703574628201198080583467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113876199008536528214889245 42703574628201198080583467)
            ·
              refine ⟨64055361942301797120875201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42703574628201198080583467 64055361942301797120875201)
              ·
                refine ⟨48041521456726347840656401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64055361942301797120875201 48041521456726347840656401)
                ·
                  refine ⟨36031141092544760880492301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48041521456726347840656401 36031141092544760880492301)
                  ·
                    refine ⟨13511677909704285330184613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36031141092544760880492301 13511677909704285330184613)
                    ·
                      refine ⟨2533439608069553499409615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13511677909704285330184613 2533439608069553499409615)
                      ·
                        rfl

theorem cell23_4933856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_4933856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933856 prefixEnd_4933856 := by exact prefixLift 4933856
  have htrace : WordTrace (prefixWord ++ tailWord_4933856) baseStart_4933856 baseEnd_4933856 := by
    simpa [prefixWord, tailWord_4933856, baseEnd_4933856] using wordTrace_append hprefix tailTrace_4933856
  have hstable : (prefixWord ++ tailWord_4933856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933856).length < 2 ^ (prefixWord ++ tailWord_4933856).sum := by decide
  have hdescent : baseEnd_4933856 < baseStart_4933856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933860 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_4933860 : Nat := 118140960795 + 4933860 * 2 ^ 59
def prefixEnd_4933860 : Nat := 4983230072969 + 3 ^ 40 * 4933860 * 2
def baseEnd_4933860 : Nat := 2533441661992171483759597

theorem tailTrace_4933860 : CollatzResearch.WordTrace tailWord_4933860 prefixEnd_4933860 2533441661992171483759597 := by
  unfold tailWord_4933860
  simp only [CollatzResearch.WordTrace]
  refine ⟨89976328952737665523707517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119968438603650220698276689 89976328952737665523707517)
  ·
    refine ⟨33741123357276624571390319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89976328952737665523707517 33741123357276624571390319)
    ·
      refine ⟨50611685035914936857085479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33741123357276624571390319 50611685035914936857085479)
      ·
        refine ⟨75917527553872405285628219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50611685035914936857085479 75917527553872405285628219)
        ·
          refine ⟨113876291330808607928442329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75917527553872405285628219 113876291330808607928442329)
          ·
            refine ⟨85407218498106455946331747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113876291330808607928442329 85407218498106455946331747)
            ·
              refine ⟨128110827747159683919497621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85407218498106455946331747 128110827747159683919497621)
              ·
                refine ⟨6005195050648110183726451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128110827747159683919497621 6005195050648110183726451)
                ·
                  refine ⟨9007792575972165275589677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6005195050648110183726451 9007792575972165275589677)
                  ·
                    refine ⟨3377922215989561978346129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9007792575972165275589677 3377922215989561978346129)
                    ·
                      refine ⟨2533441661992171483759597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3377922215989561978346129 2533441661992171483759597)
                      ·
                        rfl

theorem cell23_4933860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_4933860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933860 prefixEnd_4933860 := by exact prefixLift 4933860
  have htrace : WordTrace (prefixWord ++ tailWord_4933860) baseStart_4933860 baseEnd_4933860 := by
    simpa [prefixWord, tailWord_4933860, baseEnd_4933860] using wordTrace_append hprefix tailTrace_4933860
  have hstable : (prefixWord ++ tailWord_4933860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933860).length < 2 ^ (prefixWord ++ tailWord_4933860).sum := by decide
  have hdescent : baseEnd_4933860 < baseStart_4933860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933866 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_4933866 : Nat := 118140960795 + 4933866 * 2 ^ 59
def prefixEnd_4933866 : Nat := 4983230072969 + 3 ^ 40 * 4933866 * 2
def baseEnd_4933866 : Nat := 844481580958699486761523

theorem tailTrace_4933866 : CollatzResearch.WordTrace tailWord_4933866 prefixEnd_4933866 844481580958699486761523 := by
  unfold tailWord_4933866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988219185863398518033363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119968584495635729381422301 44988219185863398518033363)
  ·
    refine ⟨67482328778795097777050045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44988219185863398518033363 67482328778795097777050045)
    ·
      refine ⟨25305873292048161666393767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67482328778795097777050045 25305873292048161666393767)
      ·
        refine ⟨37958809938072242499590651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25305873292048161666393767 37958809938072242499590651)
        ·
          refine ⟨56938214907108363749385977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37958809938072242499590651 56938214907108363749385977)
          ·
            refine ⟨42703661180331272812039483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56938214907108363749385977 42703661180331272812039483)
            ·
              refine ⟨64055491770496909218059225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42703661180331272812039483 64055491770496909218059225)
              ·
                refine ⟨48041618827872681913544419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64055491770496909218059225 48041618827872681913544419)
                ·
                  refine ⟨72062428241809022870316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48041618827872681913544419 72062428241809022870316629)
                  ·
                    refine ⟨844481580958699486761523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72062428241809022870316629 844481580958699486761523)
                    ·
                      rfl

theorem cell23_4933866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_4933866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933866 prefixEnd_4933866 := by exact prefixLift 4933866
  have htrace : WordTrace (prefixWord ++ tailWord_4933866) baseStart_4933866 baseEnd_4933866 := by
    simpa [prefixWord, tailWord_4933866, baseEnd_4933866] using wordTrace_append hprefix tailTrace_4933866
  have hstable : (prefixWord ++ tailWord_4933866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933866).length < 2 ^ (prefixWord ++ tailWord_4933866).sum := by decide
  have hdescent : baseEnd_4933866 < baseStart_4933866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4933983 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_4933983 : Nat := 118140960795 + 4933983 * 2 ^ 59
def prefixEnd_4933983 : Nat := 4983230072969 + 3 ^ 40 * 4933983 * 2
def baseEnd_4933983 : Nat := 2533504820112674502521531

theorem tailTrace_4933983 : CollatzResearch.WordTrace tailWord_4933983 prefixEnd_4933983 2533504820112674502521531 := by
  unfold tailWord_4933983
  simp only [CollatzResearch.WordTrace]
  refine ⟨179957144084029723054142603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119971429389353148702761735 179957144084029723054142603)
  ·
    refine ⟨269935716126044584581213905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179957144084029723054142603 269935716126044584581213905)
    ·
      refine ⟨202451787094533438435910429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269935716126044584581213905 202451787094533438435910429)
      ·
        refine ⟨75919420160450039413466411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202451787094533438435910429 75919420160450039413466411)
        ·
          refine ⟨113879130240675059120199617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75919420160450039413466411 113879130240675059120199617)
          ·
            refine ⟨85409347680506294340149713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113879130240675059120199617 85409347680506294340149713)
            ·
              refine ⟨64057010760379720755112285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85409347680506294340149713 64057010760379720755112285)
              ·
                refine ⟨24021379035142395283167107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64057010760379720755112285 24021379035142395283167107)
                ·
                  refine ⟨36032068552713592924750661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24021379035142395283167107 36032068552713592924750661)
                  ·
                    refine ⟨6756012853633798673390749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36032068552713592924750661 6756012853633798673390749)
                    ·
                      refine ⟨2533504820112674502521531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6756012853633798673390749 2533504820112674502521531)
                      ·
                        rfl

theorem cell23_4933983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_4933983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4933983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4933983 prefixEnd_4933983 := by exact prefixLift 4933983
  have htrace : WordTrace (prefixWord ++ tailWord_4933983) baseStart_4933983 baseEnd_4933983 := by
    simpa [prefixWord, tailWord_4933983, baseEnd_4933983] using wordTrace_append hprefix tailTrace_4933983
  have hstable : (prefixWord ++ tailWord_4933983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4933983).length < 2 ^ (prefixWord ++ tailWord_4933983).sum := by decide
  have hdescent : baseEnd_4933983 < baseStart_4933983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4933983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934000 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_4934000 : Nat := 118140960795 + 4934000 * 2 ^ 59
def prefixEnd_4934000 : Nat := 4983230072969 + 3 ^ 40 * 4934000 * 2
def baseEnd_4934000 : Nat := 2533513549283800936008953

theorem tailTrace_4934000 : CollatzResearch.WordTrace tailWord_4934000 prefixEnd_4934000 2533513549283800936008953 := by
  unfold tailWord_4934000
  simp only [CollatzResearch.WordTrace]
  refine ⟨89978882062484067478755727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119971842749978756638340969 89978882062484067478755727)
  ·
    refine ⟨134968323093726101218133591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89978882062484067478755727 134968323093726101218133591)
    ·
      refine ⟨202452484640589151827200387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134968323093726101218133591 202452484640589151827200387)
      ·
        refine ⟨303678726960883727740800581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202452484640589151827200387 303678726960883727740800581)
        ·
          refine ⟨56939761305165698951400109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303678726960883727740800581 56939761305165698951400109)
          ·
            refine ⟨21352410489437137106775041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56939761305165698951400109 21352410489437137106775041)
            ·
              refine ⟨16014307867077852830081281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21352410489437137106775041 16014307867077852830081281)
              ·
                refine ⟨12010730900308389622560961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16014307867077852830081281 12010730900308389622560961)
                ·
                  refine ⟨9008048175231292216920721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12010730900308389622560961 9008048175231292216920721)
                  ·
                    refine ⟨6756036131423469162690541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9008048175231292216920721 6756036131423469162690541)
                    ·
                      refine ⟨2533513549283800936008953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6756036131423469162690541 2533513549283800936008953)
                      ·
                        rfl

theorem cell23_4934000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_4934000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934000 prefixEnd_4934000 := by exact prefixLift 4934000
  have htrace : WordTrace (prefixWord ++ tailWord_4934000) baseStart_4934000 baseEnd_4934000 := by
    simpa [prefixWord, tailWord_4934000, baseEnd_4934000] using wordTrace_append hprefix tailTrace_4934000
  have hstable : (prefixWord ++ tailWord_4934000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934000).length < 2 ^ (prefixWord ++ tailWord_4934000).sum := by decide
  have hdescent : baseEnd_4934000 < baseStart_4934000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934084 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4934084 : Nat := 118140960795 + 4934084 * 2 ^ 59
def prefixEnd_4934084 : Nat := 4983230072969 + 3 ^ 40 * 4934084 * 2
def baseEnd_4934084 : Nat := 844518893886259535786189

theorem tailTrace_4934084 : CollatzResearch.WordTrace tailWord_4934084 prefixEnd_4934084 844518893886259535786189 := by
  unfold tailWord_4934084
  simp only [CollatzResearch.WordTrace]
  refine ⟨89980413928331908651784653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119973885237775878202379537 89980413928331908651784653)
  ·
    refine ⟨33742655223124465744419245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89980413928331908651784653 33742655223124465744419245)
    ·
      refine ⟨12653495708671674654157217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33742655223124465744419245 12653495708671674654157217)
      ·
        refine ⟨9490121781503755990617913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12653495708671674654157217 9490121781503755990617913)
        ·
          refine ⟨7117591336127816992963435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9490121781503755990617913 7117591336127816992963435)
          ·
            refine ⟨10676387004191725489445153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117591336127816992963435 10676387004191725489445153)
            ·
              refine ⟨8007290253143794117083865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10676387004191725489445153 8007290253143794117083865)
              ·
                refine ⟨6005467689857845587812899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007290253143794117083865 6005467689857845587812899)
                ·
                  refine ⟨9008201534786768381719349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6005467689857845587812899 9008201534786768381719349)
                  ·
                    refine ⟨844518893886259535786189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9008201534786768381719349 844518893886259535786189)
                    ·
                      rfl

theorem cell23_4934084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4934084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934084 prefixEnd_4934084 := by exact prefixLift 4934084
  have htrace : WordTrace (prefixWord ++ tailWord_4934084) baseStart_4934084 baseEnd_4934084 := by
    simpa [prefixWord, tailWord_4934084, baseEnd_4934084] using wordTrace_append hprefix tailTrace_4934084
  have hstable : (prefixWord ++ tailWord_4934084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934084).length < 2 ^ (prefixWord ++ tailWord_4934084).sum := by decide
  have hdescent : baseEnd_4934084 < baseStart_4934084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934087 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_4934087 : Nat := 118140960795 + 4934087 * 2 ^ 59
def prefixEnd_4934087 : Nat := 4983230072969 + 3 ^ 40 * 4934087 * 2
def baseEnd_4934087 : Nat := 2533558222100742095621053

theorem tailTrace_4934087 : CollatzResearch.WordTrace tailWord_4934087 prefixEnd_4934087 2533558222100742095621053 := by
  unfold tailWord_4934087
  simp only [CollatzResearch.WordTrace]
  refine ⟨179960937275652948815928515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119973958183768632543952343 179960937275652948815928515)
  ·
    refine ⟨269941405913479423223892773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179960937275652948815928515 269941405913479423223892773)
    ·
      refine ⟨50614013608777391854479895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269941405913479423223892773 50614013608777391854479895)
      ·
        refine ⟨75921020413166087781719843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50614013608777391854479895 75921020413166087781719843)
        ·
          refine ⟨113881530619749131672579765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75921020413166087781719843 113881530619749131672579765)
          ·
            refine ⟨10676393495601481094304353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113881530619749131672579765 10676393495601481094304353)
            ·
              refine ⟨8007295121701110820728265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10676393495601481094304353 8007295121701110820728265)
              ·
                refine ⟨6005471341275833115546199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007295121701110820728265 6005471341275833115546199)
                ·
                  refine ⟨9008207011913749673319299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6005471341275833115546199 9008207011913749673319299)
                  ·
                    refine ⟨13512310517870624509978949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9008207011913749673319299 13512310517870624509978949)
                    ·
                      refine ⟨2533558222100742095621053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13512310517870624509978949 2533558222100742095621053)
                      ·
                        rfl

theorem cell23_4934087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_4934087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934087 prefixEnd_4934087 := by exact prefixLift 4934087
  have htrace : WordTrace (prefixWord ++ tailWord_4934087) baseStart_4934087 baseEnd_4934087 := by
    simpa [prefixWord, tailWord_4934087, baseEnd_4934087] using wordTrace_append hprefix tailTrace_4934087
  have hstable : (prefixWord ++ tailWord_4934087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934087).length < 2 ^ (prefixWord ++ tailWord_4934087).sum := by decide
  have hdescent : baseEnd_4934087 < baseStart_4934087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934123 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 7]
def baseStart_4934123 : Nat := 118140960795 + 4934123 * 2 ^ 59
def prefixEnd_4934123 : Nat := 4983230072969 + 3 ^ 40 * 4934123 * 2
def baseEnd_4934123 : Nat := 844525569134767984923629

theorem tailTrace_4934123 : CollatzResearch.WordTrace tailWord_4934123 prefixEnd_4934123 844525569134767984923629 := by
  unfold tailWord_4934123
  simp only [CollatzResearch.WordTrace]
  refine ⟨179962250303522526964239023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119974833535681684642826015 179962250303522526964239023)
  ·
    refine ⟨269943375455283790446358535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179962250303522526964239023 269943375455283790446358535)
    ·
      refine ⟨404915063182925685669537803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269943375455283790446358535 404915063182925685669537803)
      ·
        refine ⟨607372594774388528504306705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404915063182925685669537803 607372594774388528504306705)
        ·
          refine ⟨455529446080791396378230029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607372594774388528504306705 455529446080791396378230029)
          ·
            refine ⟨170823542280296773641836261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455529446080791396378230029 170823542280296773641836261)
            ·
              refine ⟨32029414177555645057844299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170823542280296773641836261 32029414177555645057844299)
              ·
                refine ⟨48044121266333467586766449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32029414177555645057844299 48044121266333467586766449)
                ·
                  refine ⟨36033090949750100690074837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48044121266333467586766449 36033090949750100690074837)
                  ·
                    refine ⟨844525569134767984923629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36033090949750100690074837 844525569134767984923629)
                    ·
                      rfl

theorem cell23_4934123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_4934123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934123 prefixEnd_4934123 := by exact prefixLift 4934123
  have htrace : WordTrace (prefixWord ++ tailWord_4934123) baseStart_4934123 baseEnd_4934123 := by
    simpa [prefixWord, tailWord_4934123, baseEnd_4934123] using wordTrace_append hprefix tailTrace_4934123
  have hstable : (prefixWord ++ tailWord_4934123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934123).length < 2 ^ (prefixWord ++ tailWord_4934123).sum := by decide
  have hdescent : baseEnd_4934123 < baseStart_4934123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934147 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 3, 3, 2]
def baseStart_4934147 : Nat := 118140960795 + 4934147 * 2 ^ 59
def prefixEnd_4934147 : Nat := 4983230072969 + 3 ^ 40 * 4934147 * 2
def baseEnd_4934147 : Nat := 2533589030940011860870777

theorem tailTrace_4934147 : CollatzResearch.WordTrace tailWord_4934147 prefixEnd_4934147 2533589030940011860870777 := by
  unfold tailWord_4934147
  simp only [CollatzResearch.WordTrace]
  refine ⟨179963125655435579063112695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119975417103623719375408463 179963125655435579063112695)
  ·
    refine ⟨269944688483153368594669043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179963125655435579063112695 269944688483153368594669043)
    ·
      refine ⟨404917032724730052892003565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269944688483153368594669043 404917032724730052892003565)
      ·
        refine ⟨151843887271773769834501337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404917032724730052892003565 151843887271773769834501337)
        ·
          refine ⟨113882915453830327375876003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151843887271773769834501337 113882915453830327375876003)
          ·
            refine ⟨170824373180745491063814005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113882915453830327375876003 170824373180745491063814005)
            ·
              refine ⟨16014784985694889787232563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170824373180745491063814005 16014784985694889787232563)
              ·
                refine ⟨24022177478542334680848845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16014784985694889787232563 24022177478542334680848845)
                ·
                  refine ⟨9008316554453375505318317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24022177478542334680848845 9008316554453375505318317)
                  ·
                    refine ⟨3378118707920015814494369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9008316554453375505318317 3378118707920015814494369)
                    ·
                      refine ⟨2533589030940011860870777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378118707920015814494369 2533589030940011860870777)
                      ·
                        rfl

theorem cell23_4934147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_4934147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934147 prefixEnd_4934147 := by exact prefixLift 4934147
  have htrace : WordTrace (prefixWord ++ tailWord_4934147) baseStart_4934147 baseEnd_4934147 := by
    simpa [prefixWord, tailWord_4934147, baseEnd_4934147] using wordTrace_append hprefix tailTrace_4934147
  have hstable : (prefixWord ++ tailWord_4934147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934147).length < 2 ^ (prefixWord ++ tailWord_4934147).sum := by decide
  have hdescent : baseEnd_4934147 < baseStart_4934147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934153 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_4934153 : Nat := 118140960795 + 4934153 * 2 ^ 59
def prefixEnd_4934153 : Nat := 4983230072969 + 3 ^ 40 * 4934153 * 2
def baseEnd_4934153 : Nat := 844530703941312945798583

theorem tailTrace_4934153 : CollatzResearch.WordTrace tailWord_4934153 prefixEnd_4934153 844530703941312945798583 := by
  unfold tailWord_4934153
  simp only [CollatzResearch.WordTrace]
  refine ⟨179963344493413842087831113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119975562995609228058554075 179963344493413842087831113)
  ·
    refine ⟨134972508370060381565873335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179963344493413842087831113 134972508370060381565873335)
    ·
      refine ⟨202458762555090572348810003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134972508370060381565873335 202458762555090572348810003)
      ·
        refine ⟨303688143832635858523215005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202458762555090572348810003 303688143832635858523215005)
        ·
          refine ⟨113883053937238446946205627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303688143832635858523215005 113883053937238446946205627)
          ·
            refine ⟨170824580905857670419308441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113883053937238446946205627 170824580905857670419308441)
            ·
              refine ⟨128118435679393252814481331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170824580905857670419308441 128118435679393252814481331)
              ·
                refine ⟨192177653519089879221721997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128118435679393252814481331 192177653519089879221721997)
                ·
                  refine ⟨72066620069658704708145749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192177653519089879221721997 72066620069658704708145749)
                  ·
                    refine ⟨844530703941312945798583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72066620069658704708145749 844530703941312945798583)
                    ·
                      rfl

theorem cell23_4934153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_4934153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934153 prefixEnd_4934153 := by exact prefixLift 4934153
  have htrace : WordTrace (prefixWord ++ tailWord_4934153) baseStart_4934153 baseEnd_4934153 := by
    simpa [prefixWord, tailWord_4934153, baseEnd_4934153] using wordTrace_append hprefix tailTrace_4934153
  have hstable : (prefixWord ++ tailWord_4934153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934153).length < 2 ^ (prefixWord ++ tailWord_4934153).sum := by decide
  have hdescent : baseEnd_4934153 < baseStart_4934153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934177 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4934177 : Nat := 118140960795 + 4934177 * 2 ^ 59
def prefixEnd_4934177 : Nat := 4983230072969 + 3 ^ 40 * 4934177 * 2
def baseEnd_4934177 : Nat := 2533604435359646743495639

theorem tailTrace_4934177 : CollatzResearch.WordTrace tailWord_4934177 prefixEnd_4934177 2533604435359646743495639 := by
  unfold tailWord_4934177
  simp only [CollatzResearch.WordTrace]
  refine ⟨179964219845326894186704785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119976146563551262791136523 179964219845326894186704785)
  ·
    refine ⟨134973164883995170640028589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179964219845326894186704785 134973164883995170640028589)
    ·
      refine ⟨50614936831498188990010721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134973164883995170640028589 50614936831498188990010721)
      ·
        refine ⟨37961202623623641742508041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50614936831498188990010721 37961202623623641742508041)
        ·
          refine ⟨28470901967717731306881031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37961202623623641742508041 28470901967717731306881031)
          ·
            refine ⟨42706352951576596960321547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28470901967717731306881031 42706352951576596960321547)
            ·
              refine ⟨64059529427364895440482321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42706352951576596960321547 64059529427364895440482321)
              ·
                refine ⟨48044647070523671580361741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64059529427364895440482321 48044647070523671580361741)
                ·
                  refine ⟨18016742651446376842635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48044647070523671580361741 18016742651446376842635653)
                  ·
                    refine ⟨3378139247146195657994185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18016742651446376842635653 3378139247146195657994185)
                    ·
                      refine ⟨2533604435359646743495639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378139247146195657994185 2533604435359646743495639)
                      ·
                        rfl

theorem cell23_4934177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4934177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934177 prefixEnd_4934177 := by exact prefixLift 4934177
  have htrace : WordTrace (prefixWord ++ tailWord_4934177) baseStart_4934177 baseEnd_4934177 := by
    simpa [prefixWord, tailWord_4934177, baseEnd_4934177] using wordTrace_append hprefix tailTrace_4934177
  have hstable : (prefixWord ++ tailWord_4934177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934177).length < 2 ^ (prefixWord ++ tailWord_4934177).sum := by decide
  have hdescent : baseEnd_4934177 < baseStart_4934177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934200 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 7]
def baseStart_4934200 : Nat := 118140960795 + 4934200 * 2 ^ 59
def prefixEnd_4934200 : Nat := 4983230072969 + 3 ^ 40 * 4934200 * 2
def baseEnd_4934200 : Nat := 281512916157188905945337

theorem tailTrace_4934200 : CollatzResearch.WordTrace tailWord_4934200 prefixEnd_4934200 281512916157188905945337 := by
  unfold tailWord_4934200
  simp only [CollatzResearch.WordTrace]
  refine ⟨89982529362121784557396027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119976705816162379409861369 89982529362121784557396027)
  ·
    refine ⟨134973794043182676836094041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89982529362121784557396027 134973794043182676836094041)
    ·
      refine ⟨101230345532387007627070531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134973794043182676836094041 101230345532387007627070531)
      ·
        refine ⟨151845518298580511440605797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101230345532387007627070531 151845518298580511440605797)
        ·
          refine ⟨28471034680983845895113587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151845518298580511440605797 28471034680983845895113587)
          ·
            refine ⟨42706552021475768842670381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28471034680983845895113587 42706552021475768842670381)
            ·
              refine ⟨16014957008053413316001393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42706552021475768842670381 16014957008053413316001393)
              ·
                refine ⟨12011217756040059987001045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16014957008053413316001393 12011217756040059987001045)
                ·
                  refine ⟨281512916157188905945337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12011217756040059987001045 281512916157188905945337)
                  ·
                    rfl

theorem cell23_4934200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_4934200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934200 prefixEnd_4934200 := by exact prefixLift 4934200
  have htrace : WordTrace (prefixWord ++ tailWord_4934200) baseStart_4934200 baseEnd_4934200 := by
    simpa [prefixWord, tailWord_4934200, baseEnd_4934200] using wordTrace_append hprefix tailTrace_4934200
  have hstable : (prefixWord ++ tailWord_4934200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934200).length < 2 ^ (prefixWord ++ tailWord_4934200).sum := by decide
  have hdescent : baseEnd_4934200 < baseStart_4934200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934228 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_4934228 : Nat := 118140960795 + 4934228 * 2 ^ 59
def prefixEnd_4934228 : Nat := 4983230072969 + 3 ^ 40 * 4934228 * 2
def baseEnd_4934228 : Nat := 2533630622873026043957905

theorem tailTrace_4934228 : CollatzResearch.WordTrace tailWord_4934228 prefixEnd_4934228 2533630622873026043957905 := by
  unfold tailWord_4934228
  simp only [CollatzResearch.WordTrace]
  refine ⟨89983039984071064948405669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119977386645428086597874225 89983039984071064948405669)
  ·
    refine ⟨16871819997013324677826063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89983039984071064948405669 16871819997013324677826063)
    ·
      refine ⟨25307729995519987016739095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16871819997013324677826063 25307729995519987016739095)
      ·
        refine ⟨37961594993279980525108643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25307729995519987016739095 37961594993279980525108643)
        ·
          refine ⟨56942392489919970787662965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37961594993279980525108643 56942392489919970787662965)
          ·
            refine ⟨5338349295929997261343403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56942392489919970787662965 5338349295929997261343403)
            ·
              refine ⟨8007523943894995892015105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5338349295929997261343403 8007523943894995892015105)
              ·
                refine ⟨6005642957921246919011329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8007523943894995892015105 6005642957921246919011329)
                ·
                  refine ⟨4504232218440935189258497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005642957921246919011329 4504232218440935189258497)
                  ·
                    refine ⟨3378174163830701391943873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4504232218440935189258497 3378174163830701391943873)
                    ·
                      refine ⟨2533630622873026043957905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378174163830701391943873 2533630622873026043957905)
                      ·
                        rfl

theorem cell23_4934228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_4934228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934228 prefixEnd_4934228 := by exact prefixLift 4934228
  have htrace : WordTrace (prefixWord ++ tailWord_4934228) baseStart_4934228 baseEnd_4934228 := by
    simpa [prefixWord, tailWord_4934228, baseEnd_4934228] using wordTrace_append hprefix tailTrace_4934228
  have hstable : (prefixWord ++ tailWord_4934228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934228).length < 2 ^ (prefixWord ++ tailWord_4934228).sum := by decide
  have hdescent : baseEnd_4934228 < baseStart_4934228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934240 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_4934240 : Nat := 118140960795 + 4934240 * 2 ^ 59
def prefixEnd_4934240 : Nat := 4983230072969 + 3 ^ 40 * 4934240 * 2
def baseEnd_4934240 : Nat := 2533636784640879997007849

theorem tailTrace_4934240 : CollatzResearch.WordTrace tailWord_4934240 prefixEnd_4934240 2533636784640879997007849 := by
  unfold tailWord_4934240
  simp only [CollatzResearch.WordTrace]
  refine ⟨89983258822049327973124087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119977678429399103964165449 89983258822049327973124087)
  ·
    refine ⟨134974888233073991959686131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89983258822049327973124087 134974888233073991959686131)
    ·
      refine ⟨202462332349610987939529197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134974888233073991959686131 202462332349610987939529197)
      ·
        refine ⟨75923374631104120477323449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202462332349610987939529197 75923374631104120477323449)
        ·
          refine ⟨56942530973328090357992587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75923374631104120477323449 56942530973328090357992587)
          ·
            refine ⟨85413796459992135536988881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56942530973328090357992587 85413796459992135536988881)
            ·
              refine ⟨64060347344994101652741661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85413796459992135536988881 64060347344994101652741661)
              ·
                refine ⟨24022630254372788119778123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64060347344994101652741661 24022630254372788119778123)
                ·
                  refine ⟨36033945381559182179667185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24022630254372788119778123 36033945381559182179667185)
                  ·
                    refine ⟨27025459036169386634750389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36033945381559182179667185 27025459036169386634750389)
                    ·
                      refine ⟨2533636784640879997007849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27025459036169386634750389 2533636784640879997007849)
                      ·
                        rfl

theorem cell23_4934240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_4934240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934240 prefixEnd_4934240 := by exact prefixLift 4934240
  have htrace : WordTrace (prefixWord ++ tailWord_4934240) baseStart_4934240 baseEnd_4934240 := by
    simpa [prefixWord, tailWord_4934240, baseEnd_4934240] using wordTrace_append hprefix tailTrace_4934240
  have hstable : (prefixWord ++ tailWord_4934240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934240).length < 2 ^ (prefixWord ++ tailWord_4934240).sum := by decide
  have hdescent : baseEnd_4934240 < baseStart_4934240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934267 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 4, 4, 2]
def baseStart_4934267 : Nat := 118140960795 + 4934267 * 2 ^ 59
def prefixEnd_4934267 : Nat := 4983230072969 + 3 ^ 40 * 4934267 * 2
def baseEnd_4934267 : Nat := 2533650648618551391370225

theorem tailTrace_4934267 : CollatzResearch.WordTrace tailWord_4934267 prefixEnd_4934267 2533650648618551391370225 := by
  unfold tailWord_4934267
  simp only [CollatzResearch.WordTrace]
  refine ⟨179967502415000839557481055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119978334943333893038320703 179967502415000839557481055)
  ·
    refine ⟨269951253622501259336221583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179967502415000839557481055 269951253622501259336221583)
    ·
      refine ⟨404926880433751889004332375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269951253622501259336221583 404926880433751889004332375)
      ·
        refine ⟨607390320650627833506498563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404926880433751889004332375 607390320650627833506498563)
        ·
          refine ⟨911085480975941750259747845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607390320650627833506498563 911085480975941750259747845)
          ·
            refine ⟨170828527682989078173702721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 911085480975941750259747845 170828527682989078173702721)
            ·
              refine ⟨128121395762241808630277041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170828527682989078173702721 128121395762241808630277041)
              ·
                refine ⟨96091046821681356472707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128121395762241808630277041 96091046821681356472707781)
                ·
                  refine ⟨18017071279065254338632709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96091046821681356472707781 18017071279065254338632709)
                  ·
                    refine ⟨3378200864824735188493633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18017071279065254338632709 3378200864824735188493633)
                    ·
                      refine ⟨2533650648618551391370225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378200864824735188493633 2533650648618551391370225)
                      ·
                        rfl

theorem cell23_4934267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4, 2].length) (baseStart_4934267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934267 prefixEnd_4934267 := by exact prefixLift 4934267
  have htrace : WordTrace (prefixWord ++ tailWord_4934267) baseStart_4934267 baseEnd_4934267 := by
    simpa [prefixWord, tailWord_4934267, baseEnd_4934267] using wordTrace_append hprefix tailTrace_4934267
  have hstable : (prefixWord ++ tailWord_4934267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934267).length < 2 ^ (prefixWord ++ tailWord_4934267).sum := by decide
  have hdescent : baseEnd_4934267 < baseStart_4934267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934287 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_4934287 : Nat := 118140960795 + 4934287 * 2 ^ 59
def prefixEnd_4934287 : Nat := 4983230072969 + 3 ^ 40 * 4934287 * 2
def baseEnd_4934287 : Nat := 2533660918231641313120133

theorem tailTrace_4934287 : CollatzResearch.WordTrace tailWord_4934287 prefixEnd_4934287 2533660918231641313120133 := by
  unfold tailWord_4934287
  simp only [CollatzResearch.WordTrace]
  refine ⟨179968231874928382973209115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119978821249952255315472743 179968231874928382973209115)
  ·
    refine ⟨269952347812392574459813673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179968231874928382973209115 269952347812392574459813673)
    ·
      refine ⟨202464260859294430844860255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269952347812392574459813673 202464260859294430844860255)
      ·
        refine ⟨303696391288941646267290383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202464260859294430844860255 303696391288941646267290383)
        ·
          refine ⟨455544586933412469400935575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303696391288941646267290383 455544586933412469400935575)
          ·
            refine ⟨683316880400118704101403363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455544586933412469400935575 683316880400118704101403363)
            ·
              refine ⟨1024975320600178056152105045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 683316880400118704101403363 1024975320600178056152105045)
              ·
                refine ⟨12011429538283336595532481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1024975320600178056152105045 12011429538283336595532481)
                ·
                  refine ⟨9008572153712502446649361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12011429538283336595532481 9008572153712502446649361)
                  ·
                    refine ⟨6756429115284376834987021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9008572153712502446649361 6756429115284376834987021)
                    ·
                      refine ⟨2533660918231641313120133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6756429115284376834987021 2533660918231641313120133)
                      ·
                        rfl

theorem cell23_4934287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_4934287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934287 prefixEnd_4934287 := by exact prefixLift 4934287
  have htrace : WordTrace (prefixWord ++ tailWord_4934287) baseStart_4934287 baseEnd_4934287 := by
    simpa [prefixWord, tailWord_4934287, baseEnd_4934287] using wordTrace_append hprefix tailTrace_4934287
  have hstable : (prefixWord ++ tailWord_4934287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934287).length < 2 ^ (prefixWord ++ tailWord_4934287).sum := by decide
  have hdescent : baseEnd_4934287 < baseStart_4934287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934367 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 1, 6]
def baseStart_4934367 : Nat := 118140960795 + 4934367 * 2 ^ 59
def prefixEnd_4934367 : Nat := 4983230072969 + 3 ^ 40 * 4934367 * 2
def baseEnd_4934367 : Nat := 844567332228000333373255

theorem tailTrace_4934367 : CollatzResearch.WordTrace tailWord_4934367 prefixEnd_4934367 844567332228000333373255 := by
  unfold tailWord_4934367
  simp only [CollatzResearch.WordTrace]
  refine ⟨179971149714638556636121355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119980766476425704424080903 179971149714638556636121355)
  ·
    refine ⟨269956724571957834954182033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179971149714638556636121355 269956724571957834954182033)
    ·
      refine ⟨202467543428968376215636525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269956724571957834954182033 202467543428968376215636525)
      ·
        refine ⟨75925328785863141080863697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202467543428968376215636525 75925328785863141080863697)
        ·
          refine ⟨56943996589397355810647773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75925328785863141080863697 56943996589397355810647773)
          ·
            refine ⟨21353998721024008428992915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56943996589397355810647773 21353998721024008428992915)
            ·
              refine ⟨32030998081536012643489373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21353998721024008428992915 32030998081536012643489373)
              ·
                refine ⟨12011624280576004741308515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32030998081536012643489373 12011624280576004741308515)
                ·
                  refine ⟨18017436420864007111962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12011624280576004741308515 18017436420864007111962773)
                  ·
                    refine ⟨844567332228000333373255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18017436420864007111962773 844567332228000333373255)
                    ·
                      rfl

theorem cell23_4934367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_4934367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934367 prefixEnd_4934367 := by exact prefixLift 4934367
  have htrace : WordTrace (prefixWord ++ tailWord_4934367) baseStart_4934367 baseEnd_4934367 := by
    simpa [prefixWord, tailWord_4934367, baseEnd_4934367] using wordTrace_append hprefix tailTrace_4934367
  have hstable : (prefixWord ++ tailWord_4934367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934367).length < 2 ^ (prefixWord ++ tailWord_4934367).sum := by decide
  have hdescent : baseEnd_4934367 < baseStart_4934367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934408 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_4934408 : Nat := 118140960795 + 4934408 * 2 ^ 59
def prefixEnd_4934408 : Nat := 4983230072969 + 3 ^ 40 * 4934408 * 2
def baseEnd_4934408 : Nat := 2533723049390835339707077

theorem tailTrace_4934408 : CollatzResearch.WordTrace tailWord_4934408 prefixEnd_4934408 2533723049390835339707077 := by
  unfold tailWord_4934408
  simp only [CollatzResearch.WordTrace]
  refine ⟨89986322553745010319181939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119981763404993347092242585 89986322553745010319181939)
  ·
    refine ⟨134979483830617515478772909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89986322553745010319181939 134979483830617515478772909)
    ·
      refine ⟨50617306436481568304539841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134979483830617515478772909 50617306436481568304539841)
      ·
        refine ⟨37962979827361176228404881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50617306436481568304539841 37962979827361176228404881)
        ·
          refine ⟨28472234870520882171303661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37962979827361176228404881 28472234870520882171303661)
          ·
            refine ⟨10677088076445330814238873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28472234870520882171303661 10677088076445330814238873)
            ·
              refine ⟨8007816057333998110679155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10677088076445330814238873 8007816057333998110679155)
              ·
                refine ⟨12011724086000997166018733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8007816057333998110679155 12011724086000997166018733)
                ·
                  refine ⟨4504396532250373937257025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12011724086000997166018733 4504396532250373937257025)
                  ·
                    refine ⟨3378297399187780452942769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4504396532250373937257025 3378297399187780452942769)
                    ·
                      refine ⟨2533723049390835339707077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378297399187780452942769 2533723049390835339707077)
                      ·
                        rfl

theorem cell23_4934408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_4934408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934408 prefixEnd_4934408 := by exact prefixLift 4934408
  have htrace : WordTrace (prefixWord ++ tailWord_4934408) baseStart_4934408 baseEnd_4934408 := by
    simpa [prefixWord, tailWord_4934408, baseEnd_4934408] using wordTrace_append hprefix tailTrace_4934408
  have hstable : (prefixWord ++ tailWord_4934408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934408).length < 2 ^ (prefixWord ++ tailWord_4934408).sum := by decide
  have hdescent : baseEnd_4934408 < baseStart_4934408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934418 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4934418 : Nat := 118140960795 + 4934418 * 2 ^ 59
def prefixEnd_4934418 : Nat := 4983230072969 + 3 ^ 40 * 4934418 * 2
def baseEnd_4934418 : Nat := 844576061399126766860677

theorem tailTrace_4934418 : CollatzResearch.WordTrace tailWord_4934418 prefixEnd_4934418 844576061399126766860677 := by
  unfold tailWord_4934418
  simp only [CollatzResearch.WordTrace]
  refine ⟨44993252459363448086556977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119982006558302528230818605 44993252459363448086556977)
  ·
    refine ⟨33744939344522586064917733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44993252459363448086556977 33744939344522586064917733)
    ·
      refine ⟨6327176127097984887172075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33744939344522586064917733 6327176127097984887172075)
      ·
        refine ⟨9490764190646977330758113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6327176127097984887172075 9490764190646977330758113)
        ·
          refine ⟨7118073142985232998068585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9490764190646977330758113 7118073142985232998068585)
          ·
            refine ⟨5338554857238924748551439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7118073142985232998068585 5338554857238924748551439)
            ·
              refine ⟨8007832285858387122827159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5338554857238924748551439 8007832285858387122827159)
              ·
                refine ⟨12011748428787580684240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8007832285858387122827159 12011748428787580684240739)
                ·
                  refine ⟨18017622643181371026361109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12011748428787580684240739 18017622643181371026361109)
                  ·
                    refine ⟨844576061399126766860677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18017622643181371026361109 844576061399126766860677)
                    ·
                      rfl

theorem cell23_4934418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4934418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934418 prefixEnd_4934418 := by exact prefixLift 4934418
  have htrace : WordTrace (prefixWord ++ tailWord_4934418) baseStart_4934418 baseEnd_4934418 := by
    simpa [prefixWord, tailWord_4934418, baseEnd_4934418] using wordTrace_append hprefix tailTrace_4934418
  have hstable : (prefixWord ++ tailWord_4934418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934418).length < 2 ^ (prefixWord ++ tailWord_4934418).sum := by decide
  have hdescent : baseEnd_4934418 < baseStart_4934418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934437 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_4934437 : Nat := 118140960795 + 4934437 * 2 ^ 59
def prefixEnd_4934437 : Nat := 4983230072969 + 3 ^ 40 * 4934437 * 2
def baseEnd_4934437 : Nat := 2533737940329815726244443

theorem tailTrace_4934437 : CollatzResearch.WordTrace tailWord_4934437 prefixEnd_4934437 2533737940329815726244443 := by
  unfold tailWord_4934437
  simp only [CollatzResearch.WordTrace]
  refine ⟨179973702824384958591169565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119982468549589972394113043 179973702824384958591169565)
  ·
    refine ⟨67490138559144359471688587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179973702824384958591169565 67490138559144359471688587)
    ·
      refine ⟨101235207838716539207532881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67490138559144359471688587 101235207838716539207532881)
      ·
        refine ⟨75926405879037404405649661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101235207838716539207532881 75926405879037404405649661)
        ·
          refine ⟨28472402204639026652118623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75926405879037404405649661 28472402204639026652118623)
          ·
            refine ⟨42708603306958539978177935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28472402204639026652118623 42708603306958539978177935)
            ·
              refine ⟨64062904960437809967266903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42708603306958539978177935 64062904960437809967266903)
              ·
                refine ⟨96094357440656714950900355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64062904960437809967266903 96094357440656714950900355)
                ·
                  refine ⟨144141536160985072426350533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96094357440656714950900355 144141536160985072426350533)
                  ·
                    refine ⟨27026538030184701079940725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 144141536160985072426350533 27026538030184701079940725)
                    ·
                      refine ⟨2533737940329815726244443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27026538030184701079940725 2533737940329815726244443)
                      ·
                        rfl

theorem cell23_4934437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_4934437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934437 prefixEnd_4934437 := by exact prefixLift 4934437
  have htrace : WordTrace (prefixWord ++ tailWord_4934437) baseStart_4934437 baseEnd_4934437 := by
    simpa [prefixWord, tailWord_4934437, baseEnd_4934437] using wordTrace_append hprefix tailTrace_4934437
  have hstable : (prefixWord ++ tailWord_4934437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934437).length < 2 ^ (prefixWord ++ tailWord_4934437).sum := by decide
  have hdescent : baseEnd_4934437 < baseStart_4934437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934467 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_4934467 : Nat := 118140960795 + 4934467 * 2 ^ 59
def prefixEnd_4934467 : Nat := 4983230072969 + 3 ^ 40 * 4934467 * 2
def baseEnd_4934467 : Nat := 2533753344749450608869305

theorem tailTrace_4934467 : CollatzResearch.WordTrace tailWord_4934467 prefixEnd_4934467 2533753344749450608869305 := by
  unfold tailWord_4934467
  simp only [CollatzResearch.WordTrace]
  refine ⟨179974797014276273714761655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119983198009517515809841103 179974797014276273714761655)
  ·
    refine ⟨269962195521414410572142483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179974797014276273714761655 269962195521414410572142483)
    ·
      refine ⟨404943293282121615858213725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269962195521414410572142483 404943293282121615858213725)
      ·
        refine ⟨151853734980795605946830147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404943293282121615858213725 151853734980795605946830147)
        ·
          refine ⟨227780602471193408920245221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151853734980795605946830147 227780602471193408920245221)
          ·
            refine ⟨42708862963348764172545979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227780602471193408920245221 42708862963348764172545979)
            ·
              refine ⟨64063294445023146258818969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42708862963348764172545979 64063294445023146258818969)
              ·
                refine ⟨48047470833767359694114227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64063294445023146258818969 48047470833767359694114227)
                ·
                  refine ⟨72071206250651039541171341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48047470833767359694114227 72071206250651039541171341)
                  ·
                    refine ⟨27026702343994139827939253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72071206250651039541171341 27026702343994139827939253)
                    ·
                      refine ⟨2533753344749450608869305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27026702343994139827939253 2533753344749450608869305)
                      ·
                        rfl

theorem cell23_4934467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_4934467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934467 prefixEnd_4934467 := by exact prefixLift 4934467
  have htrace : WordTrace (prefixWord ++ tailWord_4934467) baseStart_4934467 baseEnd_4934467 := by
    simpa [prefixWord, tailWord_4934467, baseEnd_4934467] using wordTrace_append hprefix tailTrace_4934467
  have hstable : (prefixWord ++ tailWord_4934467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934467).length < 2 ^ (prefixWord ++ tailWord_4934467).sum := by decide
  have hdescent : baseEnd_4934467 < baseStart_4934467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934497 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_4934497 : Nat := 118140960795 + 4934497 * 2 ^ 59
def prefixEnd_4934497 : Nat := 4983230072969 + 3 ^ 40 * 4934497 * 2
def baseEnd_4934497 : Nat := 2533768749169085491494167

theorem tailTrace_4934497 : CollatzResearch.WordTrace tailWord_4934497 prefixEnd_4934497 2533768749169085491494167 := by
  unfold tailWord_4934497
  simp only [CollatzResearch.WordTrace]
  refine ⟨179975891204167588838353745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119983927469445059225569163 179975891204167588838353745)
  ·
    refine ⟨134981918403125691628765309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179975891204167588838353745 134981918403125691628765309)
    ·
      refine ⟨50618219401172134360786991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134981918403125691628765309 50618219401172134360786991)
      ·
        refine ⟨75927329101758201541180487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50618219401172134360786991 75927329101758201541180487)
        ·
          refine ⟨113890993652637302311770731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75927329101758201541180487 113890993652637302311770731)
          ·
            refine ⟨170836490478955953467656097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113890993652637302311770731 170836490478955953467656097)
            ·
              refine ⟨128127367859216965100742073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170836490478955953467656097 128127367859216965100742073)
              ·
                refine ⟨96095525894412723825556555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128127367859216965100742073 96095525894412723825556555)
                ·
                  refine ⟨144143288841619085738334833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96095525894412723825556555 144143288841619085738334833)
                  ·
                    refine ⟨108107466631214314303751125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 144143288841619085738334833 108107466631214314303751125)
                    ·
                      refine ⟨2533768749169085491494167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108107466631214314303751125 2533768749169085491494167)
                      ·
                        rfl

theorem cell23_4934497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_4934497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934497 prefixEnd_4934497 := by exact prefixLift 4934497
  have htrace : WordTrace (prefixWord ++ tailWord_4934497) baseStart_4934497 baseEnd_4934497 := by
    simpa [prefixWord, tailWord_4934497, baseEnd_4934497] using wordTrace_append hprefix tailTrace_4934497
  have hstable : (prefixWord ++ tailWord_4934497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934497).length < 2 ^ (prefixWord ++ tailWord_4934497).sum := by decide
  have hdescent : baseEnd_4934497 < baseStart_4934497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934521 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 5]
def baseStart_4934521 : Nat := 118140960795 + 4934521 * 2 ^ 59
def prefixEnd_4934521 : Nat := 4983230072969 + 3 ^ 40 * 4934521 * 2
def baseEnd_4934521 : Nat := 281531230300532599732673

theorem tailTrace_4934521 : CollatzResearch.WordTrace tailWord_4934521 prefixEnd_4934521 281531230300532599732673 := by
  unfold tailWord_4934521
  simp only [CollatzResearch.WordTrace]
  refine ⟨179976766556080640937227417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119984511037387093958151611 179976766556080640937227417)
  ·
    refine ⟨134982574917060480702920563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179976766556080640937227417 134982574917060480702920563)
    ·
      refine ⟨202473862375590721054380845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134982574917060480702920563 202473862375590721054380845)
      ·
        refine ⟨75927698390846520395392817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202473862375590721054380845 75927698390846520395392817)
        ·
          refine ⟨56945773793134890296544613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75927698390846520395392817 56945773793134890296544613)
          ·
            refine ⟨10677332586212791930602115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56945773793134890296544613 10677332586212791930602115)
            ·
              refine ⟨16015998879319187895903173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10677332586212791930602115 16015998879319187895903173)
              ·
                refine ⟨3002999789872347730481845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16015998879319187895903173 3002999789872347730481845)
                ·
                  refine ⟨281531230300532599732673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002999789872347730481845 281531230300532599732673)
                  ·
                    rfl

theorem cell23_4934521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 5].length) (baseStart_4934521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934521 prefixEnd_4934521 := by exact prefixLift 4934521
  have htrace : WordTrace (prefixWord ++ tailWord_4934521) baseStart_4934521 baseEnd_4934521 := by
    simpa [prefixWord, tailWord_4934521, baseEnd_4934521] using wordTrace_append hprefix tailTrace_4934521
  have hstable : (prefixWord ++ tailWord_4934521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934521).length < 2 ^ (prefixWord ++ tailWord_4934521).sum := by decide
  have hdescent : baseEnd_4934521 < baseStart_4934521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934547 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 10]
def baseStart_4934547 : Nat := 118140960795 + 4934547 * 2 ^ 59
def prefixEnd_4934547 : Nat := 4983230072969 + 3 ^ 40 * 4934547 * 2
def baseEnd_4934547 : Nat := 844598141067270098622979

theorem tailTrace_4934547 : CollatzResearch.WordTrace tailWord_4934547 prefixEnd_4934547 844598141067270098622979 := by
  unfold tailWord_4934547
  simp only [CollatzResearch.WordTrace]
  refine ⟨179977714853986447377673895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119985143235990964918449263 179977714853986447377673895)
  ·
    refine ⟨269966572280979671066510843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179977714853986447377673895 269966572280979671066510843)
    ·
      refine ⟨404949858421469506599766265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269966572280979671066510843 404949858421469506599766265)
      ·
        refine ⟨303712393816102129949824699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404949858421469506599766265 303712393816102129949824699)
        ·
          refine ⟨455568590724153194924737049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303712393816102129949824699 455568590724153194924737049)
          ·
            refine ⟨341676443043114896193552787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455568590724153194924737049 341676443043114896193552787)
            ·
              refine ⟨512514664564672344290329181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341676443043114896193552787 512514664564672344290329181)
              ·
                refine ⟨192192999211752129108873443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512514664564672344290329181 192192999211752129108873443)
                ·
                  refine ⟨288289498817628193663310165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192192999211752129108873443 288289498817628193663310165)
                  ·
                    refine ⟨844598141067270098622979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 288289498817628193663310165 844598141067270098622979)
                    ·
                      rfl

theorem cell23_4934547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_4934547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934547 prefixEnd_4934547 := by exact prefixLift 4934547
  have htrace : WordTrace (prefixWord ++ tailWord_4934547) baseStart_4934547 baseEnd_4934547 := by
    simpa [prefixWord, tailWord_4934547, baseEnd_4934547] using wordTrace_append hprefix tailTrace_4934547
  have hstable : (prefixWord ++ tailWord_4934547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934547).length < 2 ^ (prefixWord ++ tailWord_4934547).sum := by decide
  have hdescent : baseEnd_4934547 < baseStart_4934547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934624 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_4934624 : Nat := 118140960795 + 4934624 * 2 ^ 59
def prefixEnd_4934624 : Nat := 4983230072969 + 3 ^ 40 * 4934624 * 2
def baseEnd_4934624 : Nat := 844611320404068831535361

theorem tailTrace_4934624 : CollatzResearch.WordTrace tailWord_4934624 prefixEnd_4934624 844611320404068831535361 := by
  unfold tailWord_4934624
  simp only [CollatzResearch.WordTrace]
  refine ⟨89990261637353744764113463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119987015516471659685484617 89990261637353744764113463)
  ·
    refine ⟨134985392456030617146170195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89990261637353744764113463 134985392456030617146170195)
    ·
      refine ⟨202478088684045925719255293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134985392456030617146170195 202478088684045925719255293)
      ·
        refine ⟨75929283256517222144720735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202478088684045925719255293 75929283256517222144720735)
        ·
          refine ⟨113893924884775833217081103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75929283256517222144720735 113893924884775833217081103)
          ·
            refine ⟨170840887327163749825621655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113893924884775833217081103 170840887327163749825621655)
            ·
              refine ⟨256261330990745624738432483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170840887327163749825621655 256261330990745624738432483)
              ·
                refine ⟨384391996486118437107648725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256261330990745624738432483 384391996486118437107648725)
                ·
                  refine ⟨9009187417643400869710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 384391996486118437107648725 9009187417643400869710517)
                  ·
                    refine ⟨844611320404068831535361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9009187417643400869710517 844611320404068831535361)
                    ·
                      rfl

theorem cell23_4934624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_4934624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934624 prefixEnd_4934624 := by exact prefixLift 4934624
  have htrace : WordTrace (prefixWord ++ tailWord_4934624) baseStart_4934624 baseEnd_4934624 := by
    simpa [prefixWord, tailWord_4934624, baseEnd_4934624] using wordTrace_append hprefix tailTrace_4934624
  have hstable : (prefixWord ++ tailWord_4934624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934624).length < 2 ^ (prefixWord ++ tailWord_4934624).sum := by decide
  have hdescent : baseEnd_4934624 < baseStart_4934624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934645 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 6]
def baseStart_4934645 : Nat := 118140960795 + 4934645 * 2 ^ 59
def prefixEnd_4934645 : Nat := 4983230072969 + 3 ^ 40 * 4934645 * 2
def baseEnd_4934645 : Nat := 281538304922883434715943

theorem tailTrace_4934645 : CollatzResearch.WordTrace tailWord_4934645 prefixEnd_4934645 281538304922883434715943 := by
  unfold tailWord_4934645
  simp only [CollatzResearch.WordTrace]
  refine ⟨179981289207631410114741389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119987526138420940076494259 179981289207631410114741389)
  ·
    refine ⟨67492983452861778793028021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179981289207631410114741389 67492983452861778793028021)
    ·
      refine ⟨6327467198705791761846377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67492983452861778793028021 6327467198705791761846377)
      ·
        refine ⟨4745600399029343821384783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6327467198705791761846377 4745600399029343821384783)
        ·
          refine ⟨7118400598544015732077175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4745600399029343821384783 7118400598544015732077175)
          ·
            refine ⟨10677600897816023598115763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118400598544015732077175 10677600897816023598115763)
            ·
              refine ⟨16016401346724035397173645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10677600897816023598115763 16016401346724035397173645)
              ·
                refine ⟨6006150505021513273940117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16016401346724035397173645 6006150505021513273940117)
                ·
                  refine ⟨281538304922883434715943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6006150505021513273940117 281538304922883434715943)
                  ·
                    rfl

theorem cell23_4934645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_4934645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934645 prefixEnd_4934645 := by exact prefixLift 4934645
  have htrace : WordTrace (prefixWord ++ tailWord_4934645) baseStart_4934645 baseEnd_4934645 := by
    simpa [prefixWord, tailWord_4934645, baseEnd_4934645] using wordTrace_append hprefix tailTrace_4934645
  have hstable : (prefixWord ++ tailWord_4934645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934645).length < 2 ^ (prefixWord ++ tailWord_4934645).sum := by decide
  have hdescent : baseEnd_4934645 < baseStart_4934645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934661 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_4934661 : Nat := 118140960795 + 4934661 * 2 ^ 59
def prefixEnd_4934661 : Nat := 4983230072969 + 3 ^ 40 * 4934661 * 2
def baseEnd_4934661 : Nat := 2533852959996422849843413

theorem tailTrace_4934661 : CollatzResearch.WordTrace tailWord_4934661 prefixEnd_4934661 2533852959996422849843413 := by
  unfold tailWord_4934661
  simp only [CollatzResearch.WordTrace]
  refine ⟨179981872775573444847323837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119987915183715629898215891 179981872775573444847323837)
  ·
    refine ⟨67493202290840041817746439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179981872775573444847323837 67493202290840041817746439)
    ·
      refine ⟨101239803436260062726619659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67493202290840041817746439 101239803436260062726619659)
      ·
        refine ⟨151859705154390094089929489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101239803436260062726619659 151859705154390094089929489)
        ·
          refine ⟨113894778865792570567447117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151859705154390094089929489 113894778865792570567447117)
          ·
            refine ⟨42710542074672213962792669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113894778865792570567447117 42710542074672213962792669)
            ·
              refine ⟨16016453278002080236047251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42710542074672213962792669 16016453278002080236047251)
              ·
                refine ⟨24024679917003120354070877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16016453278002080236047251 24024679917003120354070877)
                ·
                  refine ⟨9009254968876170132776579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24024679917003120354070877 9009254968876170132776579)
                  ·
                    refine ⟨13513882453314255199164869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9009254968876170132776579 13513882453314255199164869)
                    ·
                      refine ⟨2533852959996422849843413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13513882453314255199164869 2533852959996422849843413)
                      ·
                        rfl

theorem cell23_4934661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_4934661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934661 prefixEnd_4934661 := by exact prefixLift 4934661
  have htrace : WordTrace (prefixWord ++ tailWord_4934661) baseStart_4934661 baseEnd_4934661 := by
    simpa [prefixWord, tailWord_4934661, baseEnd_4934661] using wordTrace_append hprefix tailTrace_4934661
  have hstable : (prefixWord ++ tailWord_4934661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934661).length < 2 ^ (prefixWord ++ tailWord_4934661).sum := by decide
  have hdescent : baseEnd_4934661 < baseStart_4934661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934681 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_4934681 : Nat := 118140960795 + 4934681 * 2 ^ 59
def prefixEnd_4934681 : Nat := 4983230072969 + 3 ^ 40 * 4934681 * 2
def baseEnd_4934681 : Nat := 2533863229609512771593321

theorem tailTrace_4934681 : CollatzResearch.WordTrace tailWord_4934681 prefixEnd_4934681 2533863229609512771593321 := by
  unfold tailWord_4934681
  simp only [CollatzResearch.WordTrace]
  refine ⟨179982602235500988263051897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119988401490333992175367931 179982602235500988263051897)
  ·
    refine ⟨134986951676625741197288923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179982602235500988263051897 134986951676625741197288923)
    ·
      refine ⟨202480427514938611795933385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134986951676625741197288923 202480427514938611795933385)
      ·
        refine ⟨151860320636203958846950039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202480427514938611795933385 151860320636203958846950039)
        ·
          refine ⟨227790480954305938270425059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151860320636203958846950039 227790480954305938270425059)
          ·
            refine ⟨341685721431458907405637589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227790480954305938270425059 341685721431458907405637589)
            ·
              refine ⟨8008259096049818142319631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 341685721431458907405637589 8008259096049818142319631)
              ·
                refine ⟨12012388644074727213479447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008259096049818142319631 12012388644074727213479447)
                ·
                  refine ⟨18018582966112090820219171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12012388644074727213479447 18018582966112090820219171)
                  ·
                    refine ⟨27027874449168136230328757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18018582966112090820219171 27027874449168136230328757)
                    ·
                      refine ⟨2533863229609512771593321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27027874449168136230328757 2533863229609512771593321)
                      ·
                        rfl

theorem cell23_4934681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_4934681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934681 prefixEnd_4934681 := by exact prefixLift 4934681
  have htrace : WordTrace (prefixWord ++ tailWord_4934681) baseStart_4934681 baseEnd_4934681 := by
    simpa [prefixWord, tailWord_4934681, baseEnd_4934681] using wordTrace_append hprefix tailTrace_4934681
  have hstable : (prefixWord ++ tailWord_4934681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934681).length < 2 ^ (prefixWord ++ tailWord_4934681).sum := by decide
  have hdescent : baseEnd_4934681 < baseStart_4934681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934684 : List Nat := [2, 2, 3, 1, 15]
def baseStart_4934684 : Nat := 118140960795 + 4934684 * 2 ^ 59
def prefixEnd_4934684 : Nat := 4983230072969 + 3 ^ 40 * 4934684 * 2
def baseEnd_4934684 : Nat := 3475809012416291165783

theorem tailTrace_4934684 : CollatzResearch.WordTrace tailWord_4934684 prefixEnd_4934684 3475809012416291165783 := by
  unfold tailWord_4934684
  simp only [CollatzResearch.WordTrace]
  refine ⟨89991355827245059887705553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119988474436326746516940737 89991355827245059887705553)
  ·
    refine ⟨67493516870433794915779165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89991355827245059887705553 67493516870433794915779165)
    ·
      refine ⟨25310068826412673093417187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67493516870433794915779165 25310068826412673093417187)
      ·
        refine ⟨37965103239619009640125781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25310068826412673093417187 37965103239619009640125781)
        ·
          refine ⟨3475809012416291165783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 37965103239619009640125781 3475809012416291165783)
          ·
            rfl

theorem cell23_4934684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 15].length) (baseStart_4934684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934684 prefixEnd_4934684 := by exact prefixLift 4934684
  have htrace : WordTrace (prefixWord ++ tailWord_4934684) baseStart_4934684 baseEnd_4934684 := by
    simpa [prefixWord, tailWord_4934684, baseEnd_4934684] using wordTrace_append hprefix tailTrace_4934684
  have hstable : (prefixWord ++ tailWord_4934684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934684).length < 2 ^ (prefixWord ++ tailWord_4934684).sum := by decide
  have hdescent : baseEnd_4934684 < baseStart_4934684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934689 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4934689 : Nat := 118140960795 + 4934689 * 2 ^ 59
def prefixEnd_4934689 : Nat := 4983230072969 + 3 ^ 40 * 4934689 * 2
def baseEnd_4934689 : Nat := 2533867337454748740293285

theorem tailTrace_4934689 : CollatzResearch.WordTrace tailWord_4934689 prefixEnd_4934689 2533867337454748740293285 := by
  unfold tailWord_4934689
  simp only [CollatzResearch.WordTrace]
  refine ⟨179982894019472005629343121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119988596012981337086228747 179982894019472005629343121)
  ·
    refine ⟨134987170514604004222007341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179982894019472005629343121 134987170514604004222007341)
    ·
      refine ⟨50620188942976501583252753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134987170514604004222007341 50620188942976501583252753)
      ·
        refine ⟨37965141707232376187439565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50620188942976501583252753 37965141707232376187439565)
        ·
          refine ⟨14236928140212141070289837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37965141707232376187439565 14236928140212141070289837)
          ·
            refine ⟨5338848052579552901358689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14236928140212141070289837 5338848052579552901358689)
            ·
              refine ⟨4004136039434664676019017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5338848052579552901358689 4004136039434664676019017)
              ·
                refine ⟨3003102029575998507014263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4004136039434664676019017 3003102029575998507014263)
                ·
                  refine ⟨4504653044363997760521395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003102029575998507014263 4504653044363997760521395)
                  ·
                    refine ⟨6756979566545996640782093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4504653044363997760521395 6756979566545996640782093)
                    ·
                      refine ⟨2533867337454748740293285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6756979566545996640782093 2533867337454748740293285)
                      ·
                        rfl

theorem cell23_4934689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4934689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934689 prefixEnd_4934689 := by exact prefixLift 4934689
  have htrace : WordTrace (prefixWord ++ tailWord_4934689) baseStart_4934689 baseEnd_4934689 := by
    simpa [prefixWord, tailWord_4934689, baseEnd_4934689] using wordTrace_append hprefix tailTrace_4934689
  have hstable : (prefixWord ++ tailWord_4934689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934689).length < 2 ^ (prefixWord ++ tailWord_4934689).sum := by decide
  have hdescent : baseEnd_4934689 < baseStart_4934689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934728 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_4934728 : Nat := 118140960795 + 4934728 * 2 ^ 59
def prefixEnd_4934728 : Nat := 4983230072969 + 3 ^ 40 * 4934728 * 2
def baseEnd_4934728 : Nat := 2533887363200274087705605

theorem tailTrace_4934728 : CollatzResearch.WordTrace tailWord_4934728 prefixEnd_4934728 2533887363200274087705605 := by
  unfold tailWord_4934728
  simp only [CollatzResearch.WordTrace]
  refine ⟨89992158233165357645006419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119989544310887143526675225 89992158233165357645006419)
  ·
    refine ⟨134988237349748036467509629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89992158233165357645006419 134988237349748036467509629)
    ·
      refine ⟨50620589006155513675316111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134988237349748036467509629 50620589006155513675316111)
      ·
        refine ⟨75930883509233270512974167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50620589006155513675316111 75930883509233270512974167)
        ·
          refine ⟨113896325263849905769461251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75930883509233270512974167 113896325263849905769461251)
          ·
            refine ⟨170844487895774858654191877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113896325263849905769461251 170844487895774858654191877)
            ·
              refine ⟨32033341480457785997660977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170844487895774858654191877 32033341480457785997660977)
              ·
                refine ⟨24025006110343339498245733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32033341480457785997660977 24025006110343339498245733)
                ·
                  refine ⟨4504688645689376155921075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24025006110343339498245733 4504688645689376155921075)
                  ·
                    refine ⟨6757032968534064233881613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4504688645689376155921075 6757032968534064233881613)
                    ·
                      refine ⟨2533887363200274087705605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6757032968534064233881613 2533887363200274087705605)
                      ·
                        rfl

theorem cell23_4934728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_4934728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934728 prefixEnd_4934728 := by exact prefixLift 4934728
  have htrace : WordTrace (prefixWord ++ tailWord_4934728) baseStart_4934728 baseEnd_4934728 := by
    simpa [prefixWord, tailWord_4934728, baseEnd_4934728] using wordTrace_append hprefix tailTrace_4934728
  have hstable : (prefixWord ++ tailWord_4934728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934728).length < 2 ^ (prefixWord ++ tailWord_4934728).sum := by decide
  have hdescent : baseEnd_4934728 < baseStart_4934728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934761 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_4934761 : Nat := 118140960795 + 4934761 * 2 ^ 59
def prefixEnd_4934761 : Nat := 4983230072969 + 3 ^ 40 * 4934761 * 2
def baseEnd_4934761 : Nat := 844634769353957486197651

theorem tailTrace_4934761 : CollatzResearch.WordTrace tailWord_4934761 prefixEnd_4934761 844634769353957486197651 := by
  unfold tailWord_4934761
  simp only [CollatzResearch.WordTrace]
  refine ⟨179985520075211161925964137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119990346716807441283976091 179985520075211161925964137)
  ·
    refine ⟨134989140056408371444473103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179985520075211161925964137 134989140056408371444473103)
    ·
      refine ⟨202483710084612557166709655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134989140056408371444473103 202483710084612557166709655)
      ·
        refine ⟨303725565126918835750064483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202483710084612557166709655 303725565126918835750064483)
        ·
          refine ⟨455588347690378253625096725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303725565126918835750064483 455588347690378253625096725)
          ·
            refine ⟨21355703797986480638676409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 455588347690378253625096725 21355703797986480638676409)
            ·
              refine ⟨16016777848489860479007307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21355703797986480638676409 16016777848489860479007307)
              ·
                refine ⟨24025166772734790718510961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16016777848489860479007307 24025166772734790718510961)
                ·
                  refine ⟨18018875079551093038883221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24025166772734790718510961 18018875079551093038883221)
                  ·
                    refine ⟨844634769353957486197651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18018875079551093038883221 844634769353957486197651)
                    ·
                      rfl

theorem cell23_4934761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_4934761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934761 prefixEnd_4934761 := by exact prefixLift 4934761
  have htrace : WordTrace (prefixWord ++ tailWord_4934761) baseStart_4934761 baseEnd_4934761 := by
    simpa [prefixWord, tailWord_4934761, baseEnd_4934761] using wordTrace_append hprefix tailTrace_4934761
  have hstable : (prefixWord ++ tailWord_4934761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934761).length < 2 ^ (prefixWord ++ tailWord_4934761).sum := by decide
  have hdescent : baseEnd_4934761 < baseStart_4934761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934788 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4934788 : Nat := 118140960795 + 4934788 * 2 ^ 59
def prefixEnd_4934788 : Nat := 4983230072969 + 3 ^ 40 * 4934788 * 2
def baseEnd_4934788 : Nat := 2533918172039543852955329

theorem tailTrace_4934788 : CollatzResearch.WordTrace tailWord_4934788 prefixEnd_4934788 2533918172039543852955329 := by
  unfold tailWord_4934788
  simp only [CollatzResearch.WordTrace]
  refine ⟨89993252423056672768598509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119991003230742230358131345 89993252423056672768598509)
  ·
    refine ⟨33747469658646252288224441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89993252423056672768598509 33747469658646252288224441)
    ·
      refine ⟨25310602243984689216168331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33747469658646252288224441 25310602243984689216168331)
      ·
        refine ⟨37965903365977033824252497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25310602243984689216168331 37965903365977033824252497)
        ·
          refine ⟨28474427524482775368189373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37965903365977033824252497 28474427524482775368189373)
          ·
            refine ⟨10677910321681040763071015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28474427524482775368189373 10677910321681040763071015)
            ·
              refine ⟨16016865482521561144606523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10677910321681040763071015 16016865482521561144606523)
              ·
                refine ⟨24025298223782341716909785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16016865482521561144606523 24025298223782341716909785)
                ·
                  refine ⟨18018973667836756287682339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24025298223782341716909785 18018973667836756287682339)
                  ·
                    refine ⟨27028460501755134431523509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18018973667836756287682339 27028460501755134431523509)
                    ·
                      refine ⟨2533918172039543852955329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27028460501755134431523509 2533918172039543852955329)
                      ·
                        rfl

theorem cell23_4934788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4934788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934788 prefixEnd_4934788 := by exact prefixLift 4934788
  have htrace : WordTrace (prefixWord ++ tailWord_4934788) baseStart_4934788 baseEnd_4934788 := by
    simpa [prefixWord, tailWord_4934788, baseEnd_4934788] using wordTrace_append hprefix tailTrace_4934788
  have hstable : (prefixWord ++ tailWord_4934788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934788).length < 2 ^ (prefixWord ++ tailWord_4934788).sum := by decide
  have hdescent : baseEnd_4934788 < baseStart_4934788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934802 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4934802 : Nat := 118140960795 + 4934802 * 2 ^ 59
def prefixEnd_4934802 : Nat := 4983230072969 + 3 ^ 40 * 4934802 * 2
def baseEnd_4934802 : Nat := 2533925360768706798180265

theorem tailTrace_4934802 : CollatzResearch.WordTrace tailWord_4934802 prefixEnd_4934802 2533925360768706798180265 := by
  unfold tailWord_4934802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44996753867015656482051665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119991343645375083952137773 44996753867015656482051665)
  ·
    refine ⟨33747565400261742361538749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44996753867015656482051665 33747565400261742361538749)
    ·
      refine ⟨12655337025098153385577031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33747565400261742361538749 12655337025098153385577031)
      ·
        refine ⟨18983005537647230078365547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12655337025098153385577031 18983005537647230078365547)
        ·
          refine ⟨28474508306470845117548321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18983005537647230078365547 28474508306470845117548321)
          ·
            refine ⟨21355881229853133838161241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28474508306470845117548321 21355881229853133838161241)
            ·
              refine ⟨16016910922389850378620931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21355881229853133838161241 16016910922389850378620931)
              ·
                refine ⟨24025366383584775567931397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16016910922389850378620931 24025366383584775567931397)
                ·
                  refine ⟨4504756196922145418987137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24025366383584775567931397 4504756196922145418987137)
                  ·
                    refine ⟨3378567147691609064240353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4504756196922145418987137 3378567147691609064240353)
                    ·
                      refine ⟨2533925360768706798180265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378567147691609064240353 2533925360768706798180265)
                      ·
                        rfl

theorem cell23_4934802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4934802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934802 prefixEnd_4934802 := by exact prefixLift 4934802
  have htrace : WordTrace (prefixWord ++ tailWord_4934802) baseStart_4934802 baseEnd_4934802 := by
    simpa [prefixWord, tailWord_4934802, baseEnd_4934802] using wordTrace_append hprefix tailTrace_4934802
  have hstable : (prefixWord ++ tailWord_4934802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934802).length < 2 ^ (prefixWord ++ tailWord_4934802).sum := by decide
  have hdescent : baseEnd_4934802 < baseStart_4934802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934808 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 7]
def baseStart_4934808 : Nat := 118140960795 + 4934808 * 2 ^ 59
def prefixEnd_4934808 : Nat := 4983230072969 + 3 ^ 40 * 4934808 * 2
def baseEnd_4934808 : Nat := 281547604628070419411693

theorem tailTrace_4934808 : CollatzResearch.WordTrace tailWord_4934808 prefixEnd_4934808 281547604628070419411693 := by
  unfold tailWord_4934808
  simp only [CollatzResearch.WordTrace]
  refine ⟨89993617153020444476462539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119991489537360592635283385 89993617153020444476462539)
  ·
    refine ⟨134990425729530666714693809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89993617153020444476462539 134990425729530666714693809)
    ·
      refine ⟨101242819297148000036020357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134990425729530666714693809 101242819297148000036020357)
      ·
        refine ⟨18983028618215250006753817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101242819297148000036020357 18983028618215250006753817)
        ·
          refine ⟨14237271463661437505065363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18983028618215250006753817 14237271463661437505065363)
          ·
            refine ⟨21355907195492156257598045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14237271463661437505065363 21355907195492156257598045)
            ·
              refine ⟨8008465198309558596599267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21355907195492156257598045 8008465198309558596599267)
              ·
                refine ⟨12012697797464337894898901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008465198309558596599267 12012697797464337894898901)
                ·
                  refine ⟨281547604628070419411693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12012697797464337894898901 281547604628070419411693)
                  ·
                    rfl

theorem cell23_4934808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_4934808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934808 prefixEnd_4934808 := by exact prefixLift 4934808
  have htrace : WordTrace (prefixWord ++ tailWord_4934808) baseStart_4934808 baseEnd_4934808 := by
    simpa [prefixWord, tailWord_4934808, baseEnd_4934808] using wordTrace_append hprefix tailTrace_4934808
  have hstable : (prefixWord ++ tailWord_4934808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934808).length < 2 ^ (prefixWord ++ tailWord_4934808).sum := by decide
  have hdescent : baseEnd_4934808 < baseStart_4934808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934828 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_4934828 : Nat := 118140960795 + 4934828 * 2 ^ 59
def prefixEnd_4934828 : Nat := 4983230072969 + 3 ^ 40 * 4934828 * 2
def baseEnd_4934828 : Nat := 2533938711265723696455145

theorem tailTrace_4934828 : CollatzResearch.WordTrace tailWord_4934828 prefixEnd_4934828 2533938711265723696455145 := by
  unfold tailWord_4934828
  simp only [CollatzResearch.WordTrace]
  refine ⟨89993981882984216184326569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119991975843978954912435425 89993981882984216184326569)
  ·
    refine ⟨67495486412238162138244927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89993981882984216184326569 67495486412238162138244927)
    ·
      refine ⟨101243229618357243207367391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67495486412238162138244927 101243229618357243207367391)
      ·
        refine ⟨151864844427535864811051087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101243229618357243207367391 151864844427535864811051087)
        ·
          refine ⟨227797266641303797216576631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151864844427535864811051087 227797266641303797216576631)
          ·
            refine ⟨341695899961955695824864947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227797266641303797216576631 341695899961955695824864947)
            ·
              refine ⟨512543849942933543737297421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341695899961955695824864947 512543849942933543737297421)
              ·
                refine ⟨192203943728600078901486533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512543849942933543737297421 192203943728600078901486533)
                ·
                  refine ⟨36038239449112514794028725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192203943728600078901486533 36038239449112514794028725)
                  ·
                    refine ⟨3378584948354298261940193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36038239449112514794028725 3378584948354298261940193)
                    ·
                      refine ⟨2533938711265723696455145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378584948354298261940193 2533938711265723696455145)
                      ·
                        rfl

theorem cell23_4934828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_4934828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934828 prefixEnd_4934828 := by exact prefixLift 4934828
  have htrace : WordTrace (prefixWord ++ tailWord_4934828) baseStart_4934828 baseEnd_4934828 := by
    simpa [prefixWord, tailWord_4934828, baseEnd_4934828] using wordTrace_append hprefix tailTrace_4934828
  have hstable : (prefixWord ++ tailWord_4934828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934828).length < 2 ^ (prefixWord ++ tailWord_4934828).sum := by decide
  have hdescent : baseEnd_4934828 < baseStart_4934828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934895 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_4934895 : Nat := 118140960795 + 4934895 * 2 ^ 59
def prefixEnd_4934895 : Nat := 4983230072969 + 3 ^ 40 * 4934895 * 2
def baseEnd_4934895 : Nat := 2533973114469574934317337

theorem tailTrace_4934895 : CollatzResearch.WordTrace tailWord_4934895 prefixEnd_4934895 2533973114469574934317337 := by
  unfold tailWord_4934895
  simp only [CollatzResearch.WordTrace]
  refine ⟨179990407456725702811342139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119993604971150468540894759 179990407456725702811342139)
  ·
    refine ⟨269985611185088554217013209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179990407456725702811342139 269985611185088554217013209)
    ·
      refine ⟨202489208388816415662759907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269985611185088554217013209 202489208388816415662759907)
      ·
        refine ⟨303733812583224623494139861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202489208388816415662759907 303733812583224623494139861)
        ·
          refine ⟨7118761232419327113143903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 303733812583224623494139861 7118761232419327113143903)
          ·
            refine ⟨10678141848628990669715855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118761232419327113143903 10678141848628990669715855)
            ·
              refine ⟨16017212772943486004573783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10678141848628990669715855 16017212772943486004573783)
              ·
                refine ⟨24025819159415229006860675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16017212772943486004573783 24025819159415229006860675)
                ·
                  refine ⟨36038728739122843510291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24025819159415229006860675 36038728739122843510291013)
                  ·
                    refine ⟨6757261638585533158179565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36038728739122843510291013 6757261638585533158179565)
                    ·
                      refine ⟨2533973114469574934317337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6757261638585533158179565 2533973114469574934317337)
                      ·
                        rfl

theorem cell23_4934895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_4934895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934895 prefixEnd_4934895 := by exact prefixLift 4934895
  have htrace : WordTrace (prefixWord ++ tailWord_4934895) baseStart_4934895 baseEnd_4934895 := by
    simpa [prefixWord, tailWord_4934895, baseEnd_4934895] using wordTrace_append hprefix tailTrace_4934895
  have hstable : (prefixWord ++ tailWord_4934895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934895).length < 2 ^ (prefixWord ++ tailWord_4934895).sum := by decide
  have hdescent : baseEnd_4934895 < baseStart_4934895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934915 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 6]
def baseStart_4934915 : Nat := 118140960795 + 4934915 * 2 ^ 59
def prefixEnd_4934915 : Nat := 4983230072969 + 3 ^ 40 * 4934915 * 2
def baseEnd_4934915 : Nat := 281553709342518317340805

theorem tailTrace_4934915 : CollatzResearch.WordTrace tailWord_4934915 prefixEnd_4934915 281553709342518317340805 := by
  unfold tailWord_4934915
  simp only [CollatzResearch.WordTrace]
  refine ⟨179991136916653246227070199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119994091277768830818046799 179991136916653246227070199)
  ·
    refine ⟨269986705374979869340605299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179991136916653246227070199 269986705374979869340605299)
    ·
      refine ⟨404980058062469804010907949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269986705374979869340605299 404980058062469804010907949)
      ·
        refine ⟨151867521773426176504090481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 404980058062469804010907949 151867521773426176504090481)
        ·
          refine ⟨113900641330069632378067861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151867521773426176504090481 113900641330069632378067861)
          ·
            refine ⟨5339092562347014017721931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113900641330069632378067861 5339092562347014017721931)
            ·
              refine ⟨8008638843520521026582897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339092562347014017721931 8008638843520521026582897)
              ·
                refine ⟨6006479132640390769937173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8008638843520521026582897 6006479132640390769937173)
                ·
                  refine ⟨281553709342518317340805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6006479132640390769937173 281553709342518317340805)
                  ·
                    rfl

theorem cell23_4934915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 6].length) (baseStart_4934915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934915 prefixEnd_4934915 := by exact prefixLift 4934915
  have htrace : WordTrace (prefixWord ++ tailWord_4934915) baseStart_4934915 baseEnd_4934915 := by
    simpa [prefixWord, tailWord_4934915, baseEnd_4934915] using wordTrace_append hprefix tailTrace_4934915
  have hstable : (prefixWord ++ tailWord_4934915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934915).length < 2 ^ (prefixWord ++ tailWord_4934915).sum := by decide
  have hdescent : baseEnd_4934915 < baseStart_4934915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934935 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4934935 : Nat := 118140960795 + 4934935 * 2 ^ 59
def prefixEnd_4934935 : Nat := 4983230072969 + 3 ^ 40 * 4934935 * 2
def baseEnd_4934935 : Nat := 2533993653695754777817153

theorem tailTrace_4934935 : CollatzResearch.WordTrace tailWord_4934935 prefixEnd_4934935 2533993653695754777817153 := by
  unfold tailWord_4934935
  simp only [CollatzResearch.WordTrace]
  refine ⟨179991866376580789642798259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119994577584387193095198839 179991866376580789642798259)
  ·
    refine ⟨269987799564871184464197389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179991866376580789642798259 269987799564871184464197389)
    ·
      refine ⟨101245424836826694174074021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269987799564871184464197389 101245424836826694174074021)
      ·
        refine ⟨18983517156905005157638879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101245424836826694174074021 18983517156905005157638879)
        ·
          refine ⟨28475275735357507736458319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18983517156905005157638879 28475275735357507736458319)
          ·
            refine ⟨42712913603036261604687479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28475275735357507736458319 42712913603036261604687479)
            ·
              refine ⟨64069370404554392407031219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42712913603036261604687479 64069370404554392407031219)
              ·
                refine ⟨96104055606831588610546829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64069370404554392407031219 96104055606831588610546829)
                ·
                  refine ⟨36039020852561845728955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96104055606831588610546829 36039020852561845728955061)
                  ·
                    refine ⟨3378658204927673037089537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36039020852561845728955061 3378658204927673037089537)
                    ·
                      refine ⟨2533993653695754777817153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378658204927673037089537 2533993653695754777817153)
                      ·
                        rfl

theorem cell23_4934935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4934935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934935 prefixEnd_4934935 := by exact prefixLift 4934935
  have htrace : WordTrace (prefixWord ++ tailWord_4934935) baseStart_4934935 baseEnd_4934935 := by
    simpa [prefixWord, tailWord_4934935, baseEnd_4934935] using wordTrace_append hprefix tailTrace_4934935
  have hstable : (prefixWord ++ tailWord_4934935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934935).length < 2 ^ (prefixWord ++ tailWord_4934935).sum := by decide
  have hdescent : baseEnd_4934935 < baseStart_4934935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934952 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4934952 : Nat := 118140960795 + 4934952 * 2 ^ 59
def prefixEnd_4934952 : Nat := 4983230072969 + 3 ^ 40 * 4934952 * 2
def baseEnd_4934952 : Nat := 2534002382866881211304575

theorem tailTrace_4934952 : CollatzResearch.WordTrace tailWord_4934952 prefixEnd_4934952 2534002382866881211304575 := by
  unfold tailWord_4934952
  simp only [CollatzResearch.WordTrace]
  refine ⟨89996243208759600773083555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119994990945012801030778073 89996243208759600773083555)
  ·
    refine ⟨134994364813139401159625333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89996243208759600773083555 134994364813139401159625333)
    ·
      refine ⟨12655721701231818858714875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134994364813139401159625333 12655721701231818858714875)
      ·
        refine ⟨18983582551847728288072313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12655721701231818858714875 18983582551847728288072313)
        ·
          refine ⟨14237686913885796216054235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18983582551847728288072313 14237686913885796216054235)
          ·
            refine ⟨21356530370828694324081353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14237686913885796216054235 21356530370828694324081353)
            ·
              refine ⟨16017397778121520743061015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21356530370828694324081353 16017397778121520743061015)
              ·
                refine ⟨24026096667182281114591523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16017397778121520743061015 24026096667182281114591523)
                ·
                  refine ⟨36039145000773421671887285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24026096667182281114591523 36039145000773421671887285)
                  ·
                    refine ⟨3378669843822508281739433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36039145000773421671887285 3378669843822508281739433)
                    ·
                      refine ⟨2534002382866881211304575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378669843822508281739433 2534002382866881211304575)
                      ·
                        rfl

theorem cell23_4934952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4934952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934952 prefixEnd_4934952 := by exact prefixLift 4934952
  have htrace : WordTrace (prefixWord ++ tailWord_4934952) baseStart_4934952 baseEnd_4934952 := by
    simpa [prefixWord, tailWord_4934952, baseEnd_4934952] using wordTrace_append hprefix tailTrace_4934952
  have hstable : (prefixWord ++ tailWord_4934952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934952).length < 2 ^ (prefixWord ++ tailWord_4934952).sum := by decide
  have hdescent : baseEnd_4934952 < baseStart_4934952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934969 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4934969 : Nat := 118140960795 + 4934969 * 2 ^ 59
def prefixEnd_4934969 : Nat := 4983230072969 + 3 ^ 40 * 4934969 * 2
def baseEnd_4934969 : Nat := 2534011112038007644791997

theorem tailTrace_4934969 : CollatzResearch.WordTrace tailWord_4934969 prefixEnd_4934969 2534011112038007644791997 := by
  unfold tailWord_4934969
  simp only [CollatzResearch.WordTrace]
  refine ⟨179993106458457613449535961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119995404305638408966357307 179993106458457613449535961)
  ·
    refine ⟨134994829843843210087151971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179993106458457613449535961 134994829843843210087151971)
    ·
      refine ⟨202492244765764815130727957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134994829843843210087151971 202492244765764815130727957)
      ·
        refine ⟨9491823973395225709252873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 202492244765764815130727957 9491823973395225709252873)
        ·
          refine ⟨7118867980046419281939655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9491823973395225709252873 7118867980046419281939655)
          ·
            refine ⟨10678301970069628922909483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118867980046419281939655 10678301970069628922909483)
            ·
              refine ⟨16017452955104443384364225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10678301970069628922909483 16017452955104443384364225)
              ·
                refine ⟨12013089716328332538273169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16017452955104443384364225 12013089716328332538273169)
                ·
                  refine ⟨9009817287246249403704877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12013089716328332538273169 9009817287246249403704877)
                  ·
                    refine ⟨3378681482717343526389329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9009817287246249403704877 3378681482717343526389329)
                    ·
                      refine ⟨2534011112038007644791997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378681482717343526389329 2534011112038007644791997)
                      ·
                        rfl

theorem cell23_4934969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4934969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934969 prefixEnd_4934969 := by exact prefixLift 4934969
  have htrace : WordTrace (prefixWord ++ tailWord_4934969) baseStart_4934969 baseEnd_4934969 := by
    simpa [prefixWord, tailWord_4934969, baseEnd_4934969] using wordTrace_append hprefix tailTrace_4934969
  have hstable : (prefixWord ++ tailWord_4934969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934969).length < 2 ^ (prefixWord ++ tailWord_4934969).sum := by decide
  have hdescent : baseEnd_4934969 < baseStart_4934969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934975 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 4, 4]
def baseStart_4934975 : Nat := 118140960795 + 4934975 * 2 ^ 59
def prefixEnd_4934975 : Nat := 4983230072969 + 3 ^ 40 * 4934975 * 2
def baseEnd_4934975 : Nat := 844671397640644873772323

theorem tailTrace_4934975 : CollatzResearch.WordTrace tailWord_4934975 prefixEnd_4934975 844671397640644873772323 := by
  unfold tailWord_4934975
  simp only [CollatzResearch.WordTrace]
  refine ⟨179993325296435876474254379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119995550197623917649502919 179993325296435876474254379)
  ·
    refine ⟨269989987944653814711381569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179993325296435876474254379 269989987944653814711381569)
    ·
      refine ⟨202492490958490361033536177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269989987944653814711381569 202492490958490361033536177)
      ·
        refine ⟨151869368218867770775152133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202492490958490361033536177 151869368218867770775152133)
        ·
          refine ⟨28475506541037707020341025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151869368218867770775152133 28475506541037707020341025)
          ·
            refine ⟨21356629905778280265255769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28475506541037707020341025 21356629905778280265255769)
            ·
              refine ⟨16017472429333710198941827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21356629905778280265255769 16017472429333710198941827)
              ·
                refine ⟨24026208644000565298412741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16017472429333710198941827 24026208644000565298412741)
                ·
                  refine ⟨4504914120750105993452389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24026208644000565298412741 4504914120750105993452389)
                  ·
                    refine ⟨844671397640644873772323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4504914120750105993452389 844671397640644873772323)
                    ·
                      rfl

theorem cell23_4934975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_4934975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934975 prefixEnd_4934975 := by exact prefixLift 4934975
  have htrace : WordTrace (prefixWord ++ tailWord_4934975) baseStart_4934975 baseEnd_4934975 := by
    simpa [prefixWord, tailWord_4934975, baseEnd_4934975] using wordTrace_append hprefix tailTrace_4934975
  have hstable : (prefixWord ++ tailWord_4934975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934975).length < 2 ^ (prefixWord ++ tailWord_4934975).sum := by decide
  have hdescent : baseEnd_4934975 < baseStart_4934975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4934988 : List Nat := [2, 2, 1, 3, 2, 2, 1, 10]
def baseStart_4934988 : Nat := 118140960795 + 4934988 * 2 ^ 59
def prefixEnd_4934988 : Nat := 4983230072969 + 3 ^ 40 * 4934988 * 2
def baseEnd_4934988 : Nat := 93852624747053447053867

theorem tailTrace_4934988 : CollatzResearch.WordTrace tailWord_4934988 prefixEnd_4934988 93852624747053447053867 := by
  unfold tailWord_4934988
  simp only [CollatzResearch.WordTrace]
  refine ⟨89996899722694389847238809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119995866296925853129651745 89996899722694389847238809)
  ·
    refine ⟨67497674792020792385429107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89996899722694389847238809 67497674792020792385429107)
    ·
      refine ⟨101246512188031188578143661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67497674792020792385429107 101246512188031188578143661)
      ·
        refine ⟨37967442070511695716803873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101246512188031188578143661 37967442070511695716803873)
        ·
          refine ⟨28475581552883771787602905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37967442070511695716803873 28475581552883771787602905)
          ·
            refine ⟨21356686164662828840702179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28475581552883771787602905 21356686164662828840702179)
            ·
              refine ⟨32035029246994243261053269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21356686164662828840702179 32035029246994243261053269)
              ·
                refine ⟨93852624747053447053867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32035029246994243261053269 93852624747053447053867)
                ·
                  rfl

theorem cell23_4934988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 10].length) (baseStart_4934988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4934988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4934988 prefixEnd_4934988 := by exact prefixLift 4934988
  have htrace : WordTrace (prefixWord ++ tailWord_4934988) baseStart_4934988 baseEnd_4934988 := by
    simpa [prefixWord, tailWord_4934988, baseEnd_4934988] using wordTrace_append hprefix tailTrace_4934988
  have hstable : (prefixWord ++ tailWord_4934988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4934988).length < 2 ^ (prefixWord ++ tailWord_4934988).sum := by decide
  have hdescent : baseEnd_4934988 < baseStart_4934988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4934988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935002 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_4935002 : Nat := 118140960795 + 4935002 * 2 ^ 59
def prefixEnd_4935002 : Nat := 4983230072969 + 3 ^ 40 * 4935002 * 2
def baseEnd_4935002 : Nat := 2534028056899606015679345

theorem tailTrace_4935002 : CollatzResearch.WordTrace tailWord_4935002 prefixEnd_4935002 2534028056899606015679345 := by
  unfold tailWord_4935002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44998577516834515021371815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119996206711558706723658173 44998577516834515021371815)
  ·
    refine ⟨67497866275251772532057723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44998577516834515021371815 67497866275251772532057723)
    ·
      refine ⟨101246799412877658798086585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67497866275251772532057723 101246799412877658798086585)
      ·
        refine ⟨75935099559658244098564939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101246799412877658798086585 75935099559658244098564939)
        ·
          refine ⟨113902649339487366147847409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75935099559658244098564939 113902649339487366147847409)
          ·
            refine ⟨85426987004615524610885557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113902649339487366147847409 85426987004615524610885557)
            ·
              refine ⟨8008780031682705432270521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85426987004615524610885557 8008780031682705432270521)
              ·
                refine ⟨6006585023762029074202891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8008780031682705432270521 6006585023762029074202891)
                ·
                  refine ⟨9009877535643043611304337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006585023762029074202891 9009877535643043611304337)
                  ·
                    refine ⟨6757408151732282708478253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9009877535643043611304337 6757408151732282708478253)
                    ·
                      refine ⟨2534028056899606015679345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6757408151732282708478253 2534028056899606015679345)
                      ·
                        rfl

theorem cell23_4935002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_4935002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935002 prefixEnd_4935002 := by exact prefixLift 4935002
  have htrace : WordTrace (prefixWord ++ tailWord_4935002) baseStart_4935002 baseEnd_4935002 := by
    simpa [prefixWord, tailWord_4935002, baseEnd_4935002] using wordTrace_append hprefix tailTrace_4935002
  have hstable : (prefixWord ++ tailWord_4935002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935002).length < 2 ^ (prefixWord ++ tailWord_4935002).sum := by decide
  have hdescent : baseEnd_4935002 < baseStart_4935002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935022 : List Nat := [4, 1, 2, 4, 2, 10]
def baseStart_4935022 : Nat := 118140960795 + 4935022 * 2 ^ 59
def prefixEnd_4935022 : Nat := 4983230072969 + 3 ^ 40 * 4935022 * 2
def baseEnd_4935022 : Nat := 10428141261369119084071

theorem tailTrace_4935022 : CollatzResearch.WordTrace tailWord_4935022 prefixEnd_4935022 10428141261369119084071 := by
  unfold tailWord_4935022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499379940908200437651915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119996693018177069000810213 22499379940908200437651915)
  ·
    refine ⟨33749069911362300656477873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499379940908200437651915 33749069911362300656477873)
    ·
      refine ⟨25311802433521725492358405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33749069911362300656477873 25311802433521725492358405)
      ·
        refine ⟨4745962956285323529817201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25311802433521725492358405 4745962956285323529817201)
        ·
          refine ⟨3559472217213992647362901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4745962956285323529817201 3559472217213992647362901)
          ·
            refine ⟨10428141261369119084071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3559472217213992647362901 10428141261369119084071)
            ·
              rfl

theorem cell23_4935022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 10].length) (baseStart_4935022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935022 prefixEnd_4935022 := by exact prefixLift 4935022
  have htrace : WordTrace (prefixWord ++ tailWord_4935022) baseStart_4935022 baseEnd_4935022 := by
    simpa [prefixWord, tailWord_4935022, baseEnd_4935022] using wordTrace_append hprefix tailTrace_4935022
  have hstable : (prefixWord ++ tailWord_4935022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935022).length < 2 ^ (prefixWord ++ tailWord_4935022).sum := by decide
  have hdescent : baseEnd_4935022 < baseStart_4935022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935070 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4935070 : Nat := 118140960795 + 4935070 * 2 ^ 59
def prefixEnd_4935070 : Nat := 4983230072969 + 3 ^ 40 * 4935070 * 2
def baseEnd_4935070 : Nat := 2534062973584111749629033

theorem tailTrace_4935070 : CollatzResearch.WordTrace tailWord_4935070 prefixEnd_4935070 2534062973584111749629033 := by
  unfold tailWord_4935070
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499598778886463462370333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119997860154061138465975109 22499598778886463462370333)
  ·
    refine ⟨8437349542082423798388875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22499598778886463462370333 8437349542082423798388875)
    ·
      refine ⟨12656024313123635697583313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8437349542082423798388875 12656024313123635697583313)
      ·
        refine ⟨9492018234842726773187485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12656024313123635697583313 9492018234842726773187485)
        ·
          refine ⟨3559506838066022539945307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9492018234842726773187485 3559506838066022539945307)
          ·
            refine ⟨5339260257099033809917961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559506838066022539945307 5339260257099033809917961)
            ·
              refine ⟨4004445192824275357438471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5339260257099033809917961 4004445192824275357438471)
              ·
                refine ⟨6006667789236413036157707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4004445192824275357438471 6006667789236413036157707)
                ·
                  refine ⟨9010001683854619554236561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6006667789236413036157707 9010001683854619554236561)
                  ·
                    refine ⟨6757501262890964665677421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9010001683854619554236561 6757501262890964665677421)
                    ·
                      refine ⟨2534062973584111749629033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6757501262890964665677421 2534062973584111749629033)
                      ·
                        rfl

theorem cell23_4935070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4935070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935070 prefixEnd_4935070 := by exact prefixLift 4935070
  have htrace : WordTrace (prefixWord ++ tailWord_4935070) baseStart_4935070 baseEnd_4935070 := by
    simpa [prefixWord, tailWord_4935070, baseEnd_4935070] using wordTrace_append hprefix tailTrace_4935070
  have hstable : (prefixWord ++ tailWord_4935070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935070).length < 2 ^ (prefixWord ++ tailWord_4935070).sum := by decide
  have hdescent : baseEnd_4935070 < baseStart_4935070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935072 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2]
def baseStart_4935072 : Nat := 118140960795 + 4935072 * 2 ^ 59
def prefixEnd_4935072 : Nat := 4983230072969 + 3 ^ 40 * 4935072 * 2
def baseEnd_4935072 : Nat := 2534064000545420741804023

theorem tailTrace_4935072 : CollatzResearch.WordTrace tailWord_4935072 prefixEnd_4935072 2534064000545420741804023 := by
  unfold tailWord_4935072
  simp only [CollatzResearch.WordTrace]
  refine ⟨89998431588542231020267735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119997908784722974693690313 89998431588542231020267735)
  ·
    refine ⟨134997647382813346530401603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89998431588542231020267735 134997647382813346530401603)
    ·
      refine ⟨202496471074220019795602405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134997647382813346530401603 202496471074220019795602405)
      ·
        refine ⟨37968088326416253711675451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202496471074220019795602405 37968088326416253711675451)
        ·
          refine ⟨56952132489624380567513177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37968088326416253711675451 56952132489624380567513177)
          ·
            refine ⟨42714099367218285425634883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56952132489624380567513177 42714099367218285425634883)
            ·
              refine ⟨64071149050827428138452325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42714099367218285425634883 64071149050827428138452325)
              ·
                refine ⟨12013340447030142775959811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64071149050827428138452325 12013340447030142775959811)
                ·
                  refine ⟨18020010670545214163939717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12013340447030142775959811 18020010670545214163939717)
                  ·
                    refine ⟨3378752000727227655738697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18020010670545214163939717 3378752000727227655738697)
                    ·
                      refine ⟨2534064000545420741804023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378752000727227655738697 2534064000545420741804023)
                      ·
                        rfl

theorem cell23_4935072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_4935072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935072 prefixEnd_4935072 := by exact prefixLift 4935072
  have htrace : WordTrace (prefixWord ++ tailWord_4935072) baseStart_4935072 baseEnd_4935072 := by
    simpa [prefixWord, tailWord_4935072, baseEnd_4935072] using wordTrace_append hprefix tailTrace_4935072
  have hstable : (prefixWord ++ tailWord_4935072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935072).length < 2 ^ (prefixWord ++ tailWord_4935072).sum := by decide
  have hdescent : baseEnd_4935072 < baseStart_4935072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935088 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_4935088 : Nat := 118140960795 + 4935088 * 2 ^ 59
def prefixEnd_4935088 : Nat := 4983230072969 + 3 ^ 40 * 4935088 * 2
def baseEnd_4935088 : Nat := 2534072216235892679203949

theorem tailTrace_4935088 : CollatzResearch.WordTrace tailWord_4935088 prefixEnd_4935088 2534072216235892679203949 := by
  unfold tailWord_4935088
  simp only [CollatzResearch.WordTrace]
  refine ⟨89998723372513248386558959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119998297830017664515411945 89998723372513248386558959)
  ·
    refine ⟨134998085058769872579838439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89998723372513248386558959 134998085058769872579838439)
    ·
      refine ⟨202497127588154808869757659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134998085058769872579838439 202497127588154808869757659)
      ·
        refine ⟨303745691382232213304636489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202497127588154808869757659 303745691382232213304636489)
        ·
          refine ⟨227809268536674159978477367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303745691382232213304636489 227809268536674159978477367)
          ·
            refine ⟨341713902805011239967716051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227809268536674159978477367 341713902805011239967716051)
            ·
              refine ⟨512570854207516859951574077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341713902805011239967716051 512570854207516859951574077)
              ·
                refine ⟨192214070327818822481840279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 512570854207516859951574077 192214070327818822481840279)
                ·
                  refine ⟨288321105491728233722760419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192214070327818822481840279 288321105491728233722760419)
                  ·
                    refine ⟨432481658237592350584140629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 288321105491728233722760419 432481658237592350584140629)
                    ·
                      refine ⟨2534072216235892679203949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 432481658237592350584140629 2534072216235892679203949)
                      ·
                        rfl

theorem cell23_4935088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_4935088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935088 prefixEnd_4935088 := by exact prefixLift 4935088
  have htrace : WordTrace (prefixWord ++ tailWord_4935088) baseStart_4935088 baseEnd_4935088 := by
    simpa [prefixWord, tailWord_4935088, baseEnd_4935088] using wordTrace_append hprefix tailTrace_4935088
  have hstable : (prefixWord ++ tailWord_4935088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935088).length < 2 ^ (prefixWord ++ tailWord_4935088).sum := by decide
  have hdescent : baseEnd_4935088 < baseStart_4935088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935089 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_4935089 : Nat := 118140960795 + 4935089 * 2 ^ 59
def prefixEnd_4935089 : Nat := 4983230072969 + 3 ^ 40 * 4935089 * 2
def baseEnd_4935089 : Nat := 2534072729716547175291445

theorem tailTrace_4935089 : CollatzResearch.WordTrace tailWord_4935089 prefixEnd_4935089 2534072729716547175291445 := by
  unfold tailWord_4935089
  simp only [CollatzResearch.WordTrace]
  refine ⟨179997483218022873943904321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119998322145348582629269547 179997483218022873943904321)
  ·
    refine ⟨134998112413517155457928241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179997483218022873943904321 134998112413517155457928241)
    ·
      refine ⟨101248584310137866593446181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134998112413517155457928241 101248584310137866593446181)
      ·
        refine ⟨18984109558150849986271159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101248584310137866593446181 18984109558150849986271159)
        ·
          refine ⟨28476164337226274979406739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18984109558150849986271159 28476164337226274979406739)
          ·
            refine ⟨42714246505839412469110109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28476164337226274979406739 42714246505839412469110109)
            ·
              refine ⟨16017842439689779675916291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42714246505839412469110109 16017842439689779675916291)
              ·
                refine ⟨24026763659534669513874437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16017842439689779675916291 24026763659534669513874437)
                ·
                  refine ⟨4505018186162750533851457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24026763659534669513874437 4505018186162750533851457)
                  ·
                    refine ⟨3378763639622062900388593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4505018186162750533851457 3378763639622062900388593)
                    ·
                      refine ⟨2534072729716547175291445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3378763639622062900388593 2534072729716547175291445)
                      ·
                        rfl

theorem cell23_4935089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_4935089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935089 prefixEnd_4935089 := by exact prefixLift 4935089
  have htrace : WordTrace (prefixWord ++ tailWord_4935089) baseStart_4935089 baseEnd_4935089 := by
    simpa [prefixWord, tailWord_4935089, baseEnd_4935089] using wordTrace_append hprefix tailTrace_4935089
  have hstable : (prefixWord ++ tailWord_4935089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935089).length < 2 ^ (prefixWord ++ tailWord_4935089).sum := by decide
  have hdescent : baseEnd_4935089 < baseStart_4935089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935095 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 7]
def baseStart_4935095 : Nat := 118140960795 + 4935095 * 2 ^ 59
def prefixEnd_4935095 : Nat := 4983230072969 + 3 ^ 40 * 4935095 * 2
def baseEnd_4935095 : Nat := 281563978955608239090713

theorem tailTrace_4935095 : CollatzResearch.WordTrace tailWord_4935095 prefixEnd_4935095 281563978955608239090713 := by
  unfold tailWord_4935095
  simp only [CollatzResearch.WordTrace]
  refine ⟨179997702056001136968622739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119998468037334091312415159 179997702056001136968622739)
  ·
    refine ⟨269996553084001705452934109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179997702056001136968622739 269996553084001705452934109)
    ·
      refine ⟨101248707406500639544850291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 269996553084001705452934109 101248707406500639544850291)
      ·
        refine ⟨151873061109750959317275437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101248707406500639544850291 151873061109750959317275437)
        ·
          refine ⟨56952397916156609743978289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151873061109750959317275437 56952397916156609743978289)
          ·
            refine ⟨42714298437117457307983717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56952397916156609743978289 42714298437117457307983717)
            ·
              refine ⟨8008930956959523245246947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42714298437117457307983717 8008930956959523245246947)
              ·
                refine ⟨12013396435439284867870421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008930956959523245246947 12013396435439284867870421)
                ·
                  refine ⟨281563978955608239090713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12013396435439284867870421 281563978955608239090713)
                  ·
                    rfl

theorem cell23_4935095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 7].length) (baseStart_4935095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935095 prefixEnd_4935095 := by exact prefixLift 4935095
  have htrace : WordTrace (prefixWord ++ tailWord_4935095) baseStart_4935095 baseEnd_4935095 := by
    simpa [prefixWord, tailWord_4935095, baseEnd_4935095] using wordTrace_append hprefix tailTrace_4935095
  have hstable : (prefixWord ++ tailWord_4935095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935095).length < 2 ^ (prefixWord ++ tailWord_4935095).sum := by decide
  have hdescent : baseEnd_4935095 < baseStart_4935095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935125 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_4935125 : Nat := 118140960795 + 4935125 * 2 ^ 59
def prefixEnd_4935125 : Nat := 4983230072969 + 3 ^ 40 * 4935125 * 2
def baseEnd_4935125 : Nat := 844697071673369678147093

theorem tailTrace_4935125 : CollatzResearch.WordTrace tailWord_4935125 prefixEnd_4935125 844697071673369678147093 := by
  unfold tailWord_4935125
  simp only [CollatzResearch.WordTrace]
  refine ⟨179998796245892452092214829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119999197497261634728143219 179998796245892452092214829)
  ·
    refine ⟨67499548592209669534580561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179998796245892452092214829 67499548592209669534580561)
    ·
      refine ⟨50624661444157252150935421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67499548592209669534580561 50624661444157252150935421)
      ·
        refine ⟨18984248041558969556600783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50624661444157252150935421 18984248041558969556600783)
        ·
          refine ⟨28476372062338454334901175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18984248041558969556600783 28476372062338454334901175)
          ·
            refine ⟨42714558093507681502351763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28476372062338454334901175 42714558093507681502351763)
            ·
              refine ⟨64071837140261522253527645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42714558093507681502351763 64071837140261522253527645)
              ·
                refine ⟨24026938927598070845072867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64071837140261522253527645 24026938927598070845072867)
                ·
                  refine ⟨36040408391397106267609301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24026938927598070845072867 36040408391397106267609301)
                  ·
                    refine ⟨844697071673369678147093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36040408391397106267609301 844697071673369678147093)
                    ·
                      rfl

theorem cell23_4935125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_4935125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935125 prefixEnd_4935125 := by exact prefixLift 4935125
  have htrace : WordTrace (prefixWord ++ tailWord_4935125) baseStart_4935125 baseEnd_4935125 := by
    simpa [prefixWord, tailWord_4935125, baseEnd_4935125] using wordTrace_append hprefix tailTrace_4935125
  have hstable : (prefixWord ++ tailWord_4935125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935125).length < 2 ^ (prefixWord ++ tailWord_4935125).sum := by decide
  have hdescent : baseEnd_4935125 < baseStart_4935125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4935129 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 5]
def baseStart_4935129 : Nat := 118140960795 + 4935129 * 2 ^ 59
def prefixEnd_4935129 : Nat := 4983230072969 + 3 ^ 40 * 4935129 * 2
def baseEnd_4935129 : Nat := 281565918771414113199029

theorem tailTrace_4935129 : CollatzResearch.WordTrace tailWord_4935129 prefixEnd_4935129 281565918771414113199029 := by
  unfold tailWord_4935129
  simp only [CollatzResearch.WordTrace]
  refine ⟨179998942137877960775360441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119999294758585307183573627 179998942137877960775360441)
  ·
    refine ⟨134999206603408470581520331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179998942137877960775360441 134999206603408470581520331)
    ·
      refine ⟨202498809905112705872280497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134999206603408470581520331 202498809905112705872280497)
      ·
        refine ⟨151874107428834529404210373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202498809905112705872280497 151874107428834529404210373)
        ·
          refine ⟨28476395142906474263289445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151874107428834529404210373 28476395142906474263289445)
          ·
            refine ⟨5339324089294963924366771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28476395142906474263289445 5339324089294963924366771)
            ·
              refine ⟨8008986133942445886550157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339324089294963924366771 8008986133942445886550157)
              ·
                refine ⟨3003369800228417207456309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8008986133942445886550157 3003369800228417207456309)
                ·
                  refine ⟨281565918771414113199029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3003369800228417207456309 281565918771414113199029)
                  ·
                    rfl

theorem cell23_4935129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 5].length) (baseStart_4935129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4935129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4935129 prefixEnd_4935129 := by exact prefixLift 4935129
  have htrace : WordTrace (prefixWord ++ tailWord_4935129) baseStart_4935129 baseEnd_4935129 := by
    simpa [prefixWord, tailWord_4935129, baseEnd_4935129] using wordTrace_append hprefix tailTrace_4935129
  have hstable : (prefixWord ++ tailWord_4935129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4935129).length < 2 ^ (prefixWord ++ tailWord_4935129).sum := by decide
  have hdescent : baseEnd_4935129 < baseStart_4935129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4935129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
