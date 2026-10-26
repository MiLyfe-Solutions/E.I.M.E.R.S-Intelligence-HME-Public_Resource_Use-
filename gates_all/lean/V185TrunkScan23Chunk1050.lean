import V185TrunkScan23Chunk1049

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6217004 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_6217004 : Nat := 118140960795 + 6217004 * 2 ^ 59
def prefixEnd_6217004 : Nat := 4983230072969 + 3 ^ 40 * 6217004 * 2
def baseEnd_6217004 : Nat := 3192311282924899176958525

theorem tailTrace_6217004 : CollatzResearch.WordTrace tailWord_6217004 prefixEnd_6217004 3192311282924899176958525 := by
  unfold tailWord_6217004
  simp only [CollatzResearch.WordTrace]
  refine ⟨113376382184431881297853033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151168509579242508397137377 113376382184431881297853033)
  ·
    refine ⟨85032286638323910973389775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113376382184431881297853033 85032286638323910973389775)
    ·
      refine ⟨127548429957485866460084663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85032286638323910973389775 127548429957485866460084663)
      ·
        refine ⟨191322644936228799690126995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127548429957485866460084663 191322644936228799690126995)
        ·
          refine ⟨286983967404343199535190493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191322644936228799690126995 286983967404343199535190493)
          ·
            refine ⟨107618987776628699825696435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286983967404343199535190493 107618987776628699825696435)
            ·
              refine ⟨161428481664943049738544653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107618987776628699825696435 161428481664943049738544653)
              ·
                refine ⟨60535680624353643651954245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161428481664943049738544653 60535680624353643651954245)
                ·
                  refine ⟨11350440117066308184741421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60535680624353643651954245 11350440117066308184741421)
                  ·
                    refine ⟨4256415043899865569278033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11350440117066308184741421 4256415043899865569278033)
                    ·
                      refine ⟨3192311282924899176958525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256415043899865569278033 3192311282924899176958525)
                      ·
                        rfl

theorem cell23_6217004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_6217004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217004 prefixEnd_6217004 := by exact prefixLift 6217004
  have htrace : WordTrace (prefixWord ++ tailWord_6217004) baseStart_6217004 baseEnd_6217004 := by
    simpa [prefixWord, tailWord_6217004, baseEnd_6217004] using wordTrace_append hprefix tailTrace_6217004
  have hstable : (prefixWord ++ tailWord_6217004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217004).length < 2 ^ (prefixWord ++ tailWord_6217004).sum := by decide
  have hdescent : baseEnd_6217004 < baseStart_6217004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217011 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 3]
def baseStart_6217011 : Nat := 118140960795 + 6217011 * 2 ^ 59
def prefixEnd_6217011 : Nat := 4983230072969 + 3 ^ 40 * 6217011 * 2
def baseEnd_6217011 : Nat := 3192314877289480649570993

theorem tailTrace_6217011 : CollatzResearch.WordTrace tailWord_6217011 prefixEnd_6217011 3192314877289480649570993 := by
  unfold tailWord_6217011
  simp only [CollatzResearch.WordTrace]
  refine ⟨226753019679838402791210887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151168679786558935194140591 226753019679838402791210887)
  ·
    refine ⟨340129529519757604186816331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226753019679838402791210887 340129529519757604186816331)
    ·
      refine ⟨510194294279636406280224497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340129529519757604186816331 510194294279636406280224497)
      ·
        refine ⟨382645720709727304710168373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510194294279636406280224497 382645720709727304710168373)
        ·
          refine ⟨35873036316536934816578285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382645720709727304710168373 35873036316536934816578285)
          ·
            refine ⟨13452388618701350556216857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35873036316536934816578285 13452388618701350556216857)
            ·
              refine ⟨10089291464026012917162643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13452388618701350556216857 10089291464026012917162643)
              ·
                refine ⟨15133937196039019375743965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089291464026012917162643 15133937196039019375743965)
                ·
                  refine ⟨5675226448514632265903987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15133937196039019375743965 5675226448514632265903987)
                  ·
                    refine ⟨8512839672771948398855981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675226448514632265903987 8512839672771948398855981)
                    ·
                      refine ⟨3192314877289480649570993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512839672771948398855981 3192314877289480649570993)
                      ·
                        rfl

theorem cell23_6217011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_6217011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217011 prefixEnd_6217011 := by exact prefixLift 6217011
  have htrace : WordTrace (prefixWord ++ tailWord_6217011) baseStart_6217011 baseEnd_6217011 := by
    simpa [prefixWord, tailWord_6217011, baseEnd_6217011] using wordTrace_append hprefix tailTrace_6217011
  have hstable : (prefixWord ++ tailWord_6217011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217011).length < 2 ^ (prefixWord ++ tailWord_6217011).sum := by decide
  have hdescent : baseEnd_6217011 < baseStart_6217011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217028 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6217028 : Nat := 118140960795 + 6217028 * 2 ^ 59
def prefixEnd_6217028 : Nat := 4983230072969 + 3 ^ 40 * 6217028 * 2
def baseEnd_6217028 : Nat := 3192323606460607083058415

theorem tailTrace_6217028 : CollatzResearch.WordTrace tailWord_6217028 prefixEnd_6217028 3192323606460607083058415 := by
  unfold tailWord_6217028
  simp only [CollatzResearch.WordTrace]
  refine ⟨113376819860388407347289869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151169093147184543129719825 113376819860388407347289869)
  ·
    refine ⟨42516307447645652755233701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113376819860388407347289869 42516307447645652755233701)
    ·
      refine ⟨7971807646433559891606319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42516307447645652755233701 7971807646433559891606319)
      ·
        refine ⟨11957711469650339837409479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971807646433559891606319 11957711469650339837409479)
        ·
          refine ⟨17936567204475509756114219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11957711469650339837409479 17936567204475509756114219)
          ·
            refine ⟨26904850806713264634171329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17936567204475509756114219 26904850806713264634171329)
            ·
              refine ⟨20178638105034948475628497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26904850806713264634171329 20178638105034948475628497)
              ·
                refine ⟨15133978578776211356721373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20178638105034948475628497 15133978578776211356721373)
                ·
                  refine ⟨5675241967041079258770515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15133978578776211356721373 5675241967041079258770515)
                  ·
                    refine ⟨8512862950561618888155773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675241967041079258770515 8512862950561618888155773)
                    ·
                      refine ⟨3192323606460607083058415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512862950561618888155773 3192323606460607083058415)
                      ·
                        rfl

theorem cell23_6217028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6217028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217028 prefixEnd_6217028 := by exact prefixLift 6217028
  have htrace : WordTrace (prefixWord ++ tailWord_6217028) baseStart_6217028 baseEnd_6217028 := by
    simpa [prefixWord, tailWord_6217028, baseEnd_6217028] using wordTrace_append hprefix tailTrace_6217028
  have hstable : (prefixWord ++ tailWord_6217028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217028).length < 2 ^ (prefixWord ++ tailWord_6217028).sum := by decide
  have hdescent : baseEnd_6217028 < baseStart_6217028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217044 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_6217044 : Nat := 118140960795 + 6217044 * 2 ^ 59
def prefixEnd_6217044 : Nat := 4983230072969 + 3 ^ 40 * 6217044 * 2
def baseEnd_6217044 : Nat := 1064110607383693006819447

theorem tailTrace_6217044 : CollatzResearch.WordTrace tailWord_6217044 prefixEnd_6217044 1064110607383693006819447 := by
  unfold tailWord_6217044
  simp only [CollatzResearch.WordTrace]
  refine ⟨113377111644359424713581093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151169482192479232951441457 113377111644359424713581093)
  ·
    refine ⟨21258208433317392133796455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113377111644359424713581093 21258208433317392133796455)
    ·
      refine ⟨31887312649976088200694683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21258208433317392133796455 31887312649976088200694683)
      ·
        refine ⟨47830968974964132301042025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31887312649976088200694683 47830968974964132301042025)
        ·
          refine ⟨35873226731223099225781519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47830968974964132301042025 35873226731223099225781519)
          ·
            refine ⟨53809840096834648838672279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35873226731223099225781519 53809840096834648838672279)
            ·
              refine ⟨80714760145251973258008419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53809840096834648838672279 80714760145251973258008419)
              ·
                refine ⟨121072140217877959887012629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80714760145251973258008419 121072140217877959887012629)
                ·
                  refine ⟨5675256572713029369703717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121072140217877959887012629 5675256572713029369703717)
                  ·
                    refine ⟨1064110607383693006819447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675256572713029369703717 1064110607383693006819447)
                    ·
                      rfl

theorem cell23_6217044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_6217044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217044 prefixEnd_6217044 := by exact prefixLift 6217044
  have htrace : WordTrace (prefixWord ++ tailWord_6217044) baseStart_6217044 baseEnd_6217044 := by
    simpa [prefixWord, tailWord_6217044, baseEnd_6217044] using wordTrace_append hprefix tailTrace_6217044
  have hstable : (prefixWord ++ tailWord_6217044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217044).length < 2 ^ (prefixWord ++ tailWord_6217044).sum := by decide
  have hdescent : baseEnd_6217044 < baseStart_6217044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217045 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6217045 : Nat := 118140960795 + 6217045 * 2 ^ 59
def prefixEnd_6217045 : Nat := 4983230072969 + 3 ^ 40 * 6217045 * 2
def baseEnd_6217045 : Nat := 3192332335631733516545837

theorem tailTrace_6217045 : CollatzResearch.WordTrace tailWord_6217045 prefixEnd_6217045 3192332335631733516545837 := by
  unfold tailWord_6217045
  simp only [CollatzResearch.WordTrace]
  refine ⟨226754259761715226597948589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151169506507810151065299059 226754259761715226597948589)
  ·
    refine ⟨85032847410643209974230721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226754259761715226597948589 85032847410643209974230721)
    ·
      refine ⟨63774635557982407480673041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85032847410643209974230721 63774635557982407480673041)
      ·
        refine ⟨47830976668486805610504781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63774635557982407480673041 47830976668486805610504781)
        ·
          refine ⟨17936616250682552103939293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47830976668486805610504781 17936616250682552103939293)
          ·
            refine ⟨6726231094005957038977235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17936616250682552103939293 6726231094005957038977235)
            ·
              refine ⟨10089346641008935558465853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6726231094005957038977235 10089346641008935558465853)
              ·
                refine ⟨3783504990378350834424695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10089346641008935558465853 3783504990378350834424695)
                ·
                  refine ⟨5675257485567526251637043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783504990378350834424695 5675257485567526251637043)
                  ·
                    refine ⟨8512886228351289377455565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675257485567526251637043 8512886228351289377455565)
                    ·
                      refine ⟨3192332335631733516545837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512886228351289377455565 3192332335631733516545837)
                      ·
                        rfl

theorem cell23_6217045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6217045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217045 prefixEnd_6217045 := by exact prefixLift 6217045
  have htrace : WordTrace (prefixWord ++ tailWord_6217045) baseStart_6217045 baseEnd_6217045 := by
    simpa [prefixWord, tailWord_6217045, baseEnd_6217045] using wordTrace_append hprefix tailTrace_6217045
  have hstable : (prefixWord ++ tailWord_6217045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217045).length < 2 ^ (prefixWord ++ tailWord_6217045).sum := by decide
  have hdescent : baseEnd_6217045 < baseStart_6217045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217067 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3]
def baseStart_6217067 : Nat := 118140960795 + 6217067 * 2 ^ 59
def prefixEnd_6217067 : Nat := 4983230072969 + 3 ^ 40 * 6217067 * 2
def baseEnd_6217067 : Nat := 3192343632206132430470735

theorem tailTrace_6217067 : CollatzResearch.WordTrace tailWord_6217067 prefixEnd_6217067 3192343632206132430470735 := by
  unfold tailWord_6217067
  simp only [CollatzResearch.WordTrace]
  refine ⟨226755062167635524355249455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151170041445090349570166303 226755062167635524355249455)
  ·
    refine ⟨340132593251453286532874183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226755062167635524355249455 340132593251453286532874183)
    ·
      refine ⟨510198889877179929799311275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340132593251453286532874183 510198889877179929799311275)
      ·
        refine ⟨765298334815769894698966913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510198889877179929799311275 765298334815769894698966913)
        ·
          refine ⟨573973751111827421024225185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765298334815769894698966913 573973751111827421024225185)
          ·
            refine ⟨430480313333870565768168889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573973751111827421024225185 430480313333870565768168889)
            ·
              refine ⟨322860235000402924326126667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430480313333870565768168889 322860235000402924326126667)
              ·
                refine ⟨484290352500604386489190001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322860235000402924326126667 484290352500604386489190001)
                ·
                  refine ⟨363217764375453289866892501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484290352500604386489190001 363217764375453289866892501)
                  ·
                    refine ⟨8512916352549686481255293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 363217764375453289866892501 8512916352549686481255293)
                    ·
                      refine ⟨3192343632206132430470735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512916352549686481255293 3192343632206132430470735)
                      ·
                        rfl

theorem cell23_6217067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3].length) (baseStart_6217067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217067 prefixEnd_6217067 := by exact prefixLift 6217067
  have htrace : WordTrace (prefixWord ++ tailWord_6217067) baseStart_6217067 baseEnd_6217067 := by
    simpa [prefixWord, tailWord_6217067, baseEnd_6217067] using wordTrace_append hprefix tailTrace_6217067
  have hstable : (prefixWord ++ tailWord_6217067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217067).length < 2 ^ (prefixWord ++ tailWord_6217067).sum := by decide
  have hdescent : baseEnd_6217067 < baseStart_6217067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217068 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_6217068 : Nat := 118140960795 + 6217068 * 2 ^ 59
def prefixEnd_6217068 : Nat := 4983230072969 + 3 ^ 40 * 6217068 * 2
def baseEnd_6217068 : Nat := 3192344145686786926558231

theorem tailTrace_6217068 : CollatzResearch.WordTrace tailWord_6217068 prefixEnd_6217068 3192344145686786926558231 := by
  unfold tailWord_6217068
  simp only [CollatzResearch.WordTrace]
  refine ⟨113377549320315950763017929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151170065760421267684023905 113377549320315950763017929)
  ·
    refine ⟨85033161990236963072263447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113377549320315950763017929 85033161990236963072263447)
    ·
      refine ⟨127549742985355444608395171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85033161990236963072263447 127549742985355444608395171)
      ·
        refine ⟨191324614478033166912592757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127549742985355444608395171 191324614478033166912592757)
        ·
          refine ⟨17936682607315609398055571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191324614478033166912592757 17936682607315609398055571)
          ·
            refine ⟨26905023910973414097083357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17936682607315609398055571 26905023910973414097083357)
            ·
              refine ⟨10089383966615030286406259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26905023910973414097083357 10089383966615030286406259)
              ·
                refine ⟨15134075949922545429609389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089383966615030286406259 15134075949922545429609389)
                ·
                  refine ⟨5675278481220954536103521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15134075949922545429609389 5675278481220954536103521)
                  ·
                    refine ⟨4256458860915715902077641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675278481220954536103521 4256458860915715902077641)
                    ·
                      refine ⟨3192344145686786926558231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256458860915715902077641 3192344145686786926558231)
                      ·
                        rfl

theorem cell23_6217068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_6217068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217068 prefixEnd_6217068 := by exact prefixLift 6217068
  have htrace : WordTrace (prefixWord ++ tailWord_6217068) baseStart_6217068 baseEnd_6217068 := by
    simpa [prefixWord, tailWord_6217068, baseEnd_6217068] using wordTrace_append hprefix tailTrace_6217068
  have hstable : (prefixWord ++ tailWord_6217068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217068).length < 2 ^ (prefixWord ++ tailWord_6217068).sum := by decide
  have hdescent : baseEnd_6217068 < baseStart_6217068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217084 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_6217084 : Nat := 118140960795 + 6217084 * 2 ^ 59
def prefixEnd_6217084 : Nat := 4983230072969 + 3 ^ 40 * 6217084 * 2
def baseEnd_6217084 : Nat := 3192352361377258863958157

theorem tailTrace_6217084 : CollatzResearch.WordTrace tailWord_6217084 prefixEnd_6217084 3192352361377258863958157 := by
  unfold tailWord_6217084
  simp only [CollatzResearch.WordTrace]
  refine ⟨113377841104286968129309153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151170454805715957505745537 113377841104286968129309153)
  ·
    refine ⟨85033380828215226096981865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113377841104286968129309153 85033380828215226096981865)
    ·
      refine ⟨63775035621161419572736399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85033380828215226096981865 63775035621161419572736399)
      ·
        refine ⟨95662553431742129359104599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63775035621161419572736399 95662553431742129359104599)
        ·
          refine ⟨143493830147613194038656899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95662553431742129359104599 143493830147613194038656899)
          ·
            refine ⟨215240745221419791057985349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143493830147613194038656899 215240745221419791057985349)
            ·
              refine ⟨40357639729016210823372253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215240745221419791057985349 40357639729016210823372253)
              ·
                refine ⟨15134114898381079058764595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40357639729016210823372253 15134114898381079058764595)
                ·
                  refine ⟨22701172347571618588146893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15134114898381079058764595 22701172347571618588146893)
                  ·
                    refine ⟨8512939630339356970555085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22701172347571618588146893 8512939630339356970555085)
                    ·
                      refine ⟨3192352361377258863958157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8512939630339356970555085 3192352361377258863958157)
                      ·
                        rfl

theorem cell23_6217084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_6217084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217084 prefixEnd_6217084 := by exact prefixLift 6217084
  have htrace : WordTrace (prefixWord ++ tailWord_6217084) baseStart_6217084 baseEnd_6217084 := by
    simpa [prefixWord, tailWord_6217084, baseEnd_6217084] using wordTrace_append hprefix tailTrace_6217084
  have hstable : (prefixWord ++ tailWord_6217084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217084).length < 2 ^ (prefixWord ++ tailWord_6217084).sum := by decide
  have hdescent : baseEnd_6217084 < baseStart_6217084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217107 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_6217107 : Nat := 118140960795 + 6217107 * 2 ^ 59
def prefixEnd_6217107 : Nat := 4983230072969 + 3 ^ 40 * 6217107 * 2
def baseEnd_6217107 : Nat := 3192364171432312273970551

theorem tailTrace_6217107 : CollatzResearch.WordTrace tailWord_6217107 prefixEnd_6217107 3192364171432312273970551 := by
  unfold tailWord_6217107
  simp only [CollatzResearch.WordTrace]
  refine ⟨226756521087490611186705575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151171014058327074124470383 226756521087490611186705575)
  ·
    refine ⟨340134781631235916780058363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226756521087490611186705575 340134781631235916780058363)
    ·
      refine ⟨510202172446853875170087545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340134781631235916780058363 510202172446853875170087545)
      ·
        refine ⟨382651629335140406377565659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510202172446853875170087545 382651629335140406377565659)
        ·
          refine ⟨573977444002710609566348489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382651629335140406377565659 573977444002710609566348489)
          ·
            refine ⟨430483083002032957174761367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573977444002710609566348489 430483083002032957174761367)
            ·
              refine ⟨645724624503049435762142051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430483083002032957174761367 645724624503049435762142051)
              ·
                refine ⟨968586936754574153643213077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645724624503049435762142051 968586936754574153643213077)
                ·
                  refine ⟨45402512660370663452025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 968586936754574153643213077 45402512660370663452025613)
                  ·
                    refine ⟨17025942247638998794509605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45402512660370663452025613 17025942247638998794509605)
                    ·
                      refine ⟨3192364171432312273970551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17025942247638998794509605 3192364171432312273970551)
                      ·
                        rfl

theorem cell23_6217107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_6217107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217107 prefixEnd_6217107 := by exact prefixLift 6217107
  have htrace : WordTrace (prefixWord ++ tailWord_6217107) baseStart_6217107 baseEnd_6217107 := by
    simpa [prefixWord, tailWord_6217107, baseEnd_6217107] using wordTrace_append hprefix tailTrace_6217107
  have hstable : (prefixWord ++ tailWord_6217107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217107).length < 2 ^ (prefixWord ++ tailWord_6217107).sum := by decide
  have hdescent : baseEnd_6217107 < baseStart_6217107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217181 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 7]
def baseStart_6217181 : Nat := 118140960795 + 6217181 * 2 ^ 59
def prefixEnd_6217181 : Nat := 4983230072969 + 3 ^ 40 * 6217181 * 2
def baseEnd_6217181 : Nat := 354711352111193887160579

theorem tailTrace_6217181 : CollatzResearch.WordTrace tailWord_6217181 prefixEnd_6217181 354711352111193887160579 := by
  unfold tailWord_6217181
  simp only [CollatzResearch.WordTrace]
  refine ⟨226759220089222521824899397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151172813392815014549932931 226759220089222521824899397)
  ·
    refine ⟨42517353766729222842168637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226759220089222521824899397 42517353766729222842168637)
    ·
      refine ⟨15944007662523458565813239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42517353766729222842168637 15944007662523458565813239)
      ·
        refine ⟨23916011493785187848719859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15944007662523458565813239 23916011493785187848719859)
        ·
          refine ⟨35874017240677781773079789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23916011493785187848719859 35874017240677781773079789)
          ·
            refine ⟨13452756465254168164904921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35874017240677781773079789 13452756465254168164904921)
            ·
              refine ⟨10089567348940626123678691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13452756465254168164904921 10089567348940626123678691)
              ·
                refine ⟨15134351023410939185518037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089567348940626123678691 15134351023410939185518037)
                ·
                  refine ⟨354711352111193887160579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15134351023410939185518037 354711352111193887160579)
                  ·
                    rfl

theorem cell23_6217181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_6217181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217181 prefixEnd_6217181 := by exact prefixLift 6217181
  have htrace : WordTrace (prefixWord ++ tailWord_6217181) baseStart_6217181 baseEnd_6217181 := by
    simpa [prefixWord, tailWord_6217181, baseEnd_6217181] using wordTrace_append hprefix tailTrace_6217181
  have hstable : (prefixWord ++ tailWord_6217181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217181).length < 2 ^ (prefixWord ++ tailWord_6217181).sum := by decide
  have hdescent : baseEnd_6217181 < baseStart_6217181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217191 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6217191 : Nat := 118140960795 + 6217191 * 2 ^ 59
def prefixEnd_6217191 : Nat := 4983230072969 + 3 ^ 40 * 6217191 * 2
def baseEnd_6217191 : Nat := 3192407303807289945320165

theorem tailTrace_6217191 : CollatzResearch.WordTrace tailWord_6217191 prefixEnd_6217191 3192407303807289945320165 := by
  unfold tailWord_6217191
  simp only [CollatzResearch.WordTrace]
  refine ⟨226759584819186293532763427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151173056546124195688508951 226759584819186293532763427)
  ·
    refine ⟨340139377228779440299145141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226759584819186293532763427 340139377228779440299145141)
    ·
      refine ⟨31888066615198072528044857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340139377228779440299145141 31888066615198072528044857)
      ·
        refine ⟨23916049961398554396033643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31888066615198072528044857 23916049961398554396033643)
        ·
          refine ⟨35874074942097831594050465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23916049961398554396033643 35874074942097831594050465)
          ·
            refine ⟨26905556206573373695537849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35874074942097831594050465 26905556206573373695537849)
            ·
              refine ⟨20179167154930030271653387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26905556206573373695537849 20179167154930030271653387)
              ·
                refine ⟨30268750732395045407480081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20179167154930030271653387 30268750732395045407480081)
                ·
                  refine ⟨22701563049296284055610061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30268750732395045407480081 22701563049296284055610061)
                  ·
                    refine ⟨8513086143486106520853773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22701563049296284055610061 8513086143486106520853773)
                    ·
                      refine ⟨3192407303807289945320165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8513086143486106520853773 3192407303807289945320165)
                      ·
                        rfl

theorem cell23_6217191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6217191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217191 prefixEnd_6217191 := by exact prefixLift 6217191
  have htrace : WordTrace (prefixWord ++ tailWord_6217191) baseStart_6217191 baseEnd_6217191 := by
    simpa [prefixWord, tailWord_6217191, baseEnd_6217191] using wordTrace_append hprefix tailTrace_6217191
  have hstable : (prefixWord ++ tailWord_6217191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217191).length < 2 ^ (prefixWord ++ tailWord_6217191).sum := by decide
  have hdescent : baseEnd_6217191 < baseStart_6217191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217291 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 5, 2]
def baseStart_6217291 : Nat := 118140960795 + 6217291 * 2 ^ 59
def prefixEnd_6217291 : Nat := 4983230072969 + 3 ^ 40 * 6217291 * 2
def baseEnd_6217291 : Nat := 3192458651872739554069705

theorem tailTrace_6217291 : CollatzResearch.WordTrace tailWord_6217291 prefixEnd_6217291 3192458651872739554069705 := by
  unfold tailWord_6217291
  simp only [CollatzResearch.WordTrace]
  refine ⟨226763232118824010611403727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151175488079216007074269151 226763232118824010611403727)
  ·
    refine ⟨340144848178236015917105591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226763232118824010611403727 340144848178236015917105591)
    ·
      refine ⟨510217272267354023875658387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340144848178236015917105591 510217272267354023875658387)
      ·
        refine ⟨765325908401031035813487581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510217272267354023875658387 765325908401031035813487581)
        ·
          refine ⟨286997215650386638430057843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765325908401031035813487581 286997215650386638430057843)
          ·
            refine ⟨430495823475579957645086765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286997215650386638430057843 430495823475579957645086765)
            ·
              refine ⟨161435933803342484116907537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430495823475579957645086765 161435933803342484116907537)
              ·
                refine ⟨121076950352506863087680653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161435933803342484116907537 121076950352506863087680653)
                ·
                  refine ⟨45403856382190073657880245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121076950352506863087680653 45403856382190073657880245)
                  ·
                    refine ⟨4256611535830319405426273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45403856382190073657880245 4256611535830319405426273)
                    ·
                      refine ⟨3192458651872739554069705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256611535830319405426273 3192458651872739554069705)
                      ·
                        rfl

theorem cell23_6217291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5, 2].length) (baseStart_6217291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217291 prefixEnd_6217291 := by exact prefixLift 6217291
  have htrace : WordTrace (prefixWord ++ tailWord_6217291) baseStart_6217291 baseEnd_6217291 := by
    simpa [prefixWord, tailWord_6217291, baseEnd_6217291] using wordTrace_append hprefix tailTrace_6217291
  have hstable : (prefixWord ++ tailWord_6217291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217291).length < 2 ^ (prefixWord ++ tailWord_6217291).sum := by decide
  have hdescent : baseEnd_6217291 < baseStart_6217291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217292 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_6217292 : Nat := 118140960795 + 6217292 * 2 ^ 59
def prefixEnd_6217292 : Nat := 4983230072969 + 3 ^ 40 * 6217292 * 2
def baseEnd_6217292 : Nat := 1064153055117798016719067

theorem tailTrace_6217292 : CollatzResearch.WordTrace tailWord_6217292 prefixEnd_6217292 1064153055117798016719067 := by
  unfold tailWord_6217292
  simp only [CollatzResearch.WordTrace]
  refine ⟨113381634295910193891095065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151175512394546925188126753 113381634295910193891095065)
  ·
    refine ⟨85036225721932645418321299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113381634295910193891095065 85036225721932645418321299)
    ·
      refine ⟨127554338582898968127481949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85036225721932645418321299 127554338582898968127481949)
      ·
        refine ⟨47832876968587113047805731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127554338582898968127481949 47832876968587113047805731)
        ·
          refine ⟨71749315452880669571708597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47832876968587113047805731 71749315452880669571708597)
          ·
            refine ⟨6726498323707562772347681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71749315452880669571708597 6726498323707562772347681)
            ·
              refine ⟨5044873742780672079260761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6726498323707562772347681 5044873742780672079260761)
              ·
                refine ⟨3783655307085504059445571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044873742780672079260761 3783655307085504059445571)
                ·
                  refine ⟨5675482960628256089168357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783655307085504059445571 5675482960628256089168357)
                  ·
                    refine ⟨1064153055117798016719067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675482960628256089168357 1064153055117798016719067)
                    ·
                      rfl

theorem cell23_6217292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_6217292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217292 prefixEnd_6217292 := by exact prefixLift 6217292
  have htrace : WordTrace (prefixWord ++ tailWord_6217292) baseStart_6217292 baseEnd_6217292 := by
    simpa [prefixWord, tailWord_6217292, baseEnd_6217292] using wordTrace_append hprefix tailTrace_6217292
  have hstable : (prefixWord ++ tailWord_6217292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217292).length < 2 ^ (prefixWord ++ tailWord_6217292).sum := by decide
  have hdescent : baseEnd_6217292 < baseStart_6217292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217321 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_6217321 : Nat := 118140960795 + 6217321 * 2 ^ 59
def prefixEnd_6217321 : Nat := 4983230072969 + 3 ^ 40 * 6217321 * 2
def baseEnd_6217321 : Nat := 3192474056292374436694567

theorem tailTrace_6217321 : CollatzResearch.WordTrace tailWord_6217321 prefixEnd_6217321 3192474056292374436694567 := by
  unfold tailWord_6217321
  simp only [CollatzResearch.WordTrace]
  refine ⟨226764326308715325734995817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151176217539143550489997211 226764326308715325734995817)
  ·
    refine ⟨170073244731536494301246863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226764326308715325734995817 170073244731536494301246863)
    ·
      refine ⟨255109867097304741451870295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170073244731536494301246863 255109867097304741451870295)
      ·
        refine ⟨382664800645957112177805443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255109867097304741451870295 382664800645957112177805443)
        ·
          refine ⟨573997200968935668266708165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382664800645957112177805443 573997200968935668266708165)
          ·
            refine ⟨107624475181675437800007781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 573997200968935668266708165 107624475181675437800007781)
            ·
              refine ⟨20179589096564144587501459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107624475181675437800007781 20179589096564144587501459)
              ·
                refine ⟨30269383644846216881252189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20179589096564144587501459 30269383644846216881252189)
                ·
                  refine ⟨11351018866817331330469571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30269383644846216881252189 11351018866817331330469571)
                  ·
                    refine ⟨17026528300225996995704357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11351018866817331330469571 17026528300225996995704357)
                    ·
                      refine ⟨3192474056292374436694567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17026528300225996995704357 3192474056292374436694567)
                      ·
                        rfl

theorem cell23_6217321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_6217321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217321 prefixEnd_6217321 := by exact prefixLift 6217321
  have htrace : WordTrace (prefixWord ++ tailWord_6217321) baseStart_6217321 baseEnd_6217321 := by
    simpa [prefixWord, tailWord_6217321, baseEnd_6217321] using wordTrace_append hprefix tailTrace_6217321
  have hstable : (prefixWord ++ tailWord_6217321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217321).length < 2 ^ (prefixWord ++ tailWord_6217321).sum := by decide
  have hdescent : baseEnd_6217321 < baseStart_6217321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217325 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6217325 : Nat := 118140960795 + 6217325 * 2 ^ 59
def prefixEnd_6217325 : Nat := 4983230072969 + 3 ^ 40 * 6217325 * 2
def baseEnd_6217325 : Nat := 3192476110214992421044549

theorem tailTrace_6217325 : CollatzResearch.WordTrace tailWord_6217325 prefixEnd_6217325 3192476110214992421044549 := by
  unfold tailWord_6217325
  simp only [CollatzResearch.WordTrace]
  refine ⟨226764472200700834418141429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151176314800467222945427619 226764472200700834418141429)
  ·
    refine ⟨21259169268815703226700759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226764472200700834418141429 21259169268815703226700759)
    ·
      refine ⟨31888753903223554840051139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21259169268815703226700759 31888753903223554840051139)
      ·
        refine ⟨47833130854835332260076709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31888753903223554840051139 47833130854835332260076709)
        ·
          refine ⟨8968712035281624798764383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47833130854835332260076709 8968712035281624798764383)
          ·
            refine ⟨13453068052922437198146575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8968712035281624798764383 13453068052922437198146575)
            ·
              refine ⟨20179602079383655797219863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13453068052922437198146575 20179602079383655797219863)
              ·
                refine ⟨30269403119075483695829795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20179602079383655797219863 30269403119075483695829795)
                ·
                  refine ⟨45404104678613225543744693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30269403119075483695829795 45404104678613225543744693)
                  ·
                    refine ⟨4256634813619989894726065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45404104678613225543744693 4256634813619989894726065)
                    ·
                      refine ⟨3192476110214992421044549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256634813619989894726065 3192476110214992421044549)
                      ·
                        rfl

theorem cell23_6217325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6217325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217325 prefixEnd_6217325 := by exact prefixLift 6217325
  have htrace : WordTrace (prefixWord ++ tailWord_6217325) baseStart_6217325 baseEnd_6217325 := by
    simpa [prefixWord, tailWord_6217325, baseEnd_6217325] using wordTrace_append hprefix tailTrace_6217325
  have hstable : (prefixWord ++ tailWord_6217325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217325).length < 2 ^ (prefixWord ++ tailWord_6217325).sum := by decide
  have hdescent : baseEnd_6217325 < baseStart_6217325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217344 : List Nat := [2, 1, 1, 2, 1, 4, 12]
def baseStart_6217344 : Nat := 118140960795 + 6217344 * 2 ^ 59
def prefixEnd_6217344 : Nat := 4983230072969 + 3 ^ 40 * 6217344 * 2
def baseEnd_6217344 : Nat := 39413405757375652428481

theorem tailTrace_6217344 : CollatzResearch.WordTrace tailWord_6217344 prefixEnd_6217344 39413405757375652428481 := by
  unfold tailWord_6217344
  simp only [CollatzResearch.WordTrace]
  refine ⟨113382582593816000331541543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151176776791754667108722057 113382582593816000331541543)
  ·
    refine ⟨170073873890724000497312315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113382582593816000331541543 170073873890724000497312315)
    ·
      refine ⟨255110810836086000745968473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170073873890724000497312315 255110810836086000745968473)
      ·
        refine ⟨191333108127064500559476355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255110810836086000745968473 191333108127064500559476355)
        ·
          refine ⟨286999662190596750839214533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191333108127064500559476355 286999662190596750839214533)
          ·
            refine ⟨53812436660736890782352725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286999662190596750839214533 53812436660736890782352725)
            ·
              refine ⟨39413405757375652428481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 53812436660736890782352725 39413405757375652428481)
              ·
                rfl

theorem cell23_6217344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 12].length) (baseStart_6217344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217344 prefixEnd_6217344 := by exact prefixLift 6217344
  have htrace : WordTrace (prefixWord ++ tailWord_6217344) baseStart_6217344 baseEnd_6217344 := by
    simpa [prefixWord, tailWord_6217344, baseEnd_6217344] using wordTrace_append hprefix tailTrace_6217344
  have hstable : (prefixWord ++ tailWord_6217344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217344).length < 2 ^ (prefixWord ++ tailWord_6217344).sum := by decide
  have hdescent : baseEnd_6217344 < baseStart_6217344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217355 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 3, 2, 2]
def baseStart_6217355 : Nat := 118140960795 + 6217355 * 2 ^ 59
def prefixEnd_6217355 : Nat := 4983230072969 + 3 ^ 40 * 6217355 * 2
def baseEnd_6217355 : Nat := 3192491514634627303669411

theorem tailTrace_6217355 : CollatzResearch.WordTrace tailWord_6217355 prefixEnd_6217355 3192491514634627303669411 := by
  unfold tailWord_6217355
  simp only [CollatzResearch.WordTrace]
  refine ⟨226765566390592149541733519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151177044260394766361155679 226765566390592149541733519)
  ·
    refine ⟨340148349585888224312600279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226765566390592149541733519 340148349585888224312600279)
    ·
      refine ⟨510222524378832336468900419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340148349585888224312600279 510222524378832336468900419)
      ·
        refine ⟨765333786568248504703350629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510222524378832336468900419 765333786568248504703350629)
        ·
          refine ⟨143500084981546594631878243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 765333786568248504703350629 143500084981546594631878243)
          ·
            refine ⟨215250127472319891947817365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143500084981546594631878243 215250127472319891947817365)
            ·
              refine ⟨10089849725264994935053939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215250127472319891947817365 10089849725264994935053939)
              ·
                refine ⟨15134774587897492402580909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089849725264994935053939 15134774587897492402580909)
                ·
                  refine ⟨5675540470461559650967841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15134774587897492402580909 5675540470461559650967841)
                  ·
                    refine ⟨4256655352846169738225881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675540470461559650967841 4256655352846169738225881)
                    ·
                      refine ⟨3192491514634627303669411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256655352846169738225881 3192491514634627303669411)
                      ·
                        rfl

theorem cell23_6217355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 2, 2].length) (baseStart_6217355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217355 prefixEnd_6217355 := by exact prefixLift 6217355
  have htrace : WordTrace (prefixWord ++ tailWord_6217355) baseStart_6217355 baseEnd_6217355 := by
    simpa [prefixWord, tailWord_6217355, baseEnd_6217355] using wordTrace_append hprefix tailTrace_6217355
  have hstable : (prefixWord ++ tailWord_6217355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217355).length < 2 ^ (prefixWord ++ tailWord_6217355).sum := by decide
  have hdescent : baseEnd_6217355 < baseStart_6217355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217358 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6217358 : Nat := 118140960795 + 6217358 * 2 ^ 59
def prefixEnd_6217358 : Nat := 4983230072969 + 3 ^ 40 * 6217358 * 2
def baseEnd_6217358 : Nat := 3192493055076590791931897

theorem tailTrace_6217358 : CollatzResearch.WordTrace tailWord_6217358 prefixEnd_6217358 3192493055076590791931897 := by
  unfold tailWord_6217358
  simp only [CollatzResearch.WordTrace]
  refine ⟨28345709476197660131761591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151177117206387520702728485 28345709476197660131761591)
  ·
    refine ⟨42518564214296490197642387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28345709476197660131761591 42518564214296490197642387)
    ·
      refine ⟨63777846321444735296463581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42518564214296490197642387 63777846321444735296463581)
      ·
        refine ⟨23916692370541775736173843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63777846321444735296463581 23916692370541775736173843)
        ·
          refine ⟨35875038555812663604260765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23916692370541775736173843 35875038555812663604260765)
          ·
            refine ⟨13453139458429748851597787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35875038555812663604260765 13453139458429748851597787)
            ·
              refine ⟨20179709187644623277396681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13453139458429748851597787 20179709187644623277396681)
              ·
                refine ⟨15134781890733467458047511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20179709187644623277396681 15134781890733467458047511)
                ·
                  refine ⟨22702172836100201187071267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15134781890733467458047511 22702172836100201187071267)
                  ·
                    refine ⟨34053259254150301780606901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22702172836100201187071267 34053259254150301780606901)
                    ·
                      refine ⟨3192493055076590791931897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34053259254150301780606901 3192493055076590791931897)
                      ·
                        rfl

theorem cell23_6217358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6217358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217358 prefixEnd_6217358 := by exact prefixLift 6217358
  have htrace : WordTrace (prefixWord ++ tailWord_6217358) baseStart_6217358 baseEnd_6217358 := by
    simpa [prefixWord, tailWord_6217358, baseEnd_6217358] using wordTrace_append hprefix tailTrace_6217358
  have hstable : (prefixWord ++ tailWord_6217358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217358).length < 2 ^ (prefixWord ++ tailWord_6217358).sum := by decide
  have hdescent : baseEnd_6217358 < baseStart_6217358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217368 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6217368 : Nat := 118140960795 + 6217368 * 2 ^ 59
def prefixEnd_6217368 : Nat := 4983230072969 + 3 ^ 40 * 6217368 * 2
def baseEnd_6217368 : Nat := 3192498189883135752806851

theorem tailTrace_6217368 : CollatzResearch.WordTrace tailWord_6217368 prefixEnd_6217368 3192498189883135752806851 := by
  unfold tailWord_6217368
  simp only [CollatzResearch.WordTrace]
  refine ⟨113383020269772526380978379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151177360359696701841304505 113383020269772526380978379)
  ·
    refine ⟨170074530404658789571467569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113383020269772526380978379 170074530404658789571467569)
    ·
      refine ⟨127555897803494092178600677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170074530404658789571467569 127555897803494092178600677)
      ·
        refine ⟨23916730838155142283487627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127555897803494092178600677 23916730838155142283487627)
        ·
          refine ⟨35875096257232713425231441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23916730838155142283487627 35875096257232713425231441)
          ·
            refine ⟨26906322192924535068923581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35875096257232713425231441 26906322192924535068923581)
            ·
              refine ⟨10089870822346700650846343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26906322192924535068923581 10089870822346700650846343)
              ·
                refine ⟨15134806233520050976269515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10089870822346700650846343 15134806233520050976269515)
                ·
                  refine ⟨22702209350280076464404273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15134806233520050976269515 22702209350280076464404273)
                  ·
                    refine ⟨17026657012710057348303205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22702209350280076464404273 17026657012710057348303205)
                    ·
                      refine ⟨3192498189883135752806851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17026657012710057348303205 3192498189883135752806851)
                      ·
                        rfl

theorem cell23_6217368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6217368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217368 prefixEnd_6217368 := by exact prefixLift 6217368
  have htrace : WordTrace (prefixWord ++ tailWord_6217368) baseStart_6217368 baseEnd_6217368 := by
    simpa [prefixWord, tailWord_6217368, baseEnd_6217368] using wordTrace_append hprefix tailTrace_6217368
  have hstable : (prefixWord ++ tailWord_6217368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217368).length < 2 ^ (prefixWord ++ tailWord_6217368).sum := by decide
  have hdescent : baseEnd_6217368 < baseStart_6217368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217405 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_6217405 : Nat := 118140960795 + 6217405 * 2 ^ 59
def prefixEnd_6217405 : Nat := 4983230072969 + 3 ^ 40 * 6217405 * 2
def baseEnd_6217405 : Nat := 3192517188667352108044181

theorem tailTrace_6217405 : CollatzResearch.WordTrace tailWord_6217405 prefixEnd_6217405 3192517188667352108044181 := by
  unfold tailWord_6217405
  simp only [CollatzResearch.WordTrace]
  refine ⟨226767390040411008081053669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151178260026940672054035779 226767390040411008081053669)
  ·
    refine ⟨42518885632577064015197563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226767390040411008081053669 42518885632577064015197563)
    ·
      refine ⟨63778328448865596022796345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42518885632577064015197563 63778328448865596022796345)
      ·
        refine ⟨47833746336649197017097259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63778328448865596022796345 47833746336649197017097259)
        ·
          refine ⟨71750619504973795525645889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47833746336649197017097259 71750619504973795525645889)
          ·
            refine ⟨53812964628730346644234417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71750619504973795525645889 53812964628730346644234417)
            ·
              refine ⟨40359723471547759983175813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53812964628730346644234417 40359723471547759983175813)
              ·
                refine ⟨7567448150915204996845465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40359723471547759983175813 7567448150915204996845465)
                ·
                  refine ⟨5675586113186403747634099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7567448150915204996845465 5675586113186403747634099)
                  ·
                    refine ⟨8513379169779605621451149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675586113186403747634099 8513379169779605621451149)
                    ·
                      refine ⟨3192517188667352108044181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8513379169779605621451149 3192517188667352108044181)
                      ·
                        rfl

theorem cell23_6217405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_6217405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217405 prefixEnd_6217405 := by exact prefixLift 6217405
  have htrace : WordTrace (prefixWord ++ tailWord_6217405) baseStart_6217405 baseEnd_6217405 := by
    simpa [prefixWord, tailWord_6217405, baseEnd_6217405] using wordTrace_append hprefix tailTrace_6217405
  have hstable : (prefixWord ++ tailWord_6217405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217405).length < 2 ^ (prefixWord ++ tailWord_6217405).sum := by decide
  have hdescent : baseEnd_6217405 < baseStart_6217405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217406 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_6217406 : Nat := 118140960795 + 6217406 * 2 ^ 59
def prefixEnd_6217406 : Nat := 4983230072969 + 3 ^ 40 * 6217406 * 2
def baseEnd_6217406 : Nat := 3192517702148006604131677

theorem tailTrace_6217406 : CollatzResearch.WordTrace tailWord_6217406 prefixEnd_6217406 3192517702148006604131677 := by
  unfold tailWord_6217406
  simp only [CollatzResearch.WordTrace]
  refine ⟨28345928314175923156480009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151178284342271590167893381 28345928314175923156480009)
  ·
    refine ⟨21259446235631942367360007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28345928314175923156480009 21259446235631942367360007)
    ·
      refine ⟨31889169353447913551040011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21259446235631942367360007 31889169353447913551040011)
      ·
        refine ⟨47833754030171870326560017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31889169353447913551040011 47833754030171870326560017)
        ·
          refine ⟨35875315522628902744920013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47833754030171870326560017 35875315522628902744920013)
          ·
            refine ⟨13453243320985838529345005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35875315522628902744920013 13453243320985838529345005)
            ·
              refine ⟨5044966245369689448504377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13453243320985838529345005 5044966245369689448504377)
              ·
                refine ⟨3783724684027267086378283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044966245369689448504377 3783724684027267086378283)
                ·
                  refine ⟨5675587026040900629567425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783724684027267086378283 5675587026040900629567425)
                  ·
                    refine ⟨4256690269530675472175569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675587026040900629567425 4256690269530675472175569)
                    ·
                      refine ⟨3192517702148006604131677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256690269530675472175569 3192517702148006604131677)
                      ·
                        rfl

theorem cell23_6217406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_6217406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217406 prefixEnd_6217406 := by exact prefixLift 6217406
  have htrace : WordTrace (prefixWord ++ tailWord_6217406) baseStart_6217406 baseEnd_6217406 := by
    simpa [prefixWord, tailWord_6217406, baseEnd_6217406] using wordTrace_append hprefix tailTrace_6217406
  have hstable : (prefixWord ++ tailWord_6217406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217406).length < 2 ^ (prefixWord ++ tailWord_6217406).sum := by decide
  have hdescent : baseEnd_6217406 < baseStart_6217406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217431 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_6217431 : Nat := 118140960795 + 6217431 * 2 ^ 59
def prefixEnd_6217431 : Nat := 4983230072969 + 3 ^ 40 * 6217431 * 2
def baseEnd_6217431 : Nat := 3192530539164369006319061

theorem tailTrace_6217431 : CollatzResearch.WordTrace tailWord_6217431 prefixEnd_6217431 3192530539164369006319061 := by
  unfold tailWord_6217431
  simp only [CollatzResearch.WordTrace]
  refine ⟨226768338338316814521500147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151178892225544543014333431 226768338338316814521500147)
  ·
    refine ⟨340152507507475221782250221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226768338338316814521500147 340152507507475221782250221)
    ·
      refine ⟨127557190315303208168343833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340152507507475221782250221 127557190315303208168343833)
      ·
        refine ⟨95667892736477406126257875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127557190315303208168343833 95667892736477406126257875)
        ·
          refine ⟨143501839104716109189386813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95667892736477406126257875 143501839104716109189386813)
          ·
            refine ⟨53813189664268540946020055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143501839104716109189386813 53813189664268540946020055)
            ·
              refine ⟨80719784496402811419030083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53813189664268540946020055 80719784496402811419030083)
              ·
                refine ⟨121079676744604217128545125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80719784496402811419030083 121079676744604217128545125)
                ·
                  refine ⟨22702439389613290711602211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121079676744604217128545125 22702439389613290711602211)
                  ·
                    refine ⟨34053659084419936067403317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22702439389613290711602211 34053659084419936067403317)
                    ·
                      refine ⟨3192530539164369006319061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34053659084419936067403317 3192530539164369006319061)
                      ·
                        rfl

theorem cell23_6217431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_6217431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217431 prefixEnd_6217431 := by exact prefixLift 6217431
  have htrace : WordTrace (prefixWord ++ tailWord_6217431) baseStart_6217431 baseEnd_6217431 := by
    simpa [prefixWord, tailWord_6217431, baseEnd_6217431] using wordTrace_append hprefix tailTrace_6217431
  have hstable : (prefixWord ++ tailWord_6217431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217431).length < 2 ^ (prefixWord ++ tailWord_6217431).sum := by decide
  have hdescent : baseEnd_6217431 < baseStart_6217431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217445 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6217445 : Nat := 118140960795 + 6217445 * 2 ^ 59
def prefixEnd_6217445 : Nat := 4983230072969 + 3 ^ 40 * 6217445 * 2
def baseEnd_6217445 : Nat := 3192537727893531951543997

theorem tailTrace_6217445 : CollatzResearch.WordTrace tailWord_6217445 prefixEnd_6217445 3192537727893531951543997 := by
  unfold tailWord_6217445
  simp only [CollatzResearch.WordTrace]
  refine ⟨226768848960266094912509789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151179232640177396608339859 226768848960266094912509789)
  ·
    refine ⟨85038318360099785592191171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226768848960266094912509789 85038318360099785592191171)
    ·
      refine ⟨127557477540149678388286757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85038318360099785592191171 127557477540149678388286757)
      ·
        refine ⟨23917027038778064697803767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127557477540149678388286757 23917027038778064697803767)
        ·
          refine ⟨35875540558167097046705651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23917027038778064697803767 35875540558167097046705651)
          ·
            refine ⟨53813310837250645570058477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35875540558167097046705651 53813310837250645570058477)
            ·
              refine ⟨20179991563968992088771929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53813310837250645570058477 20179991563968992088771929)
              ·
                refine ⟨15134993672976744066578947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20179991563968992088771929 15134993672976744066578947)
                ·
                  refine ⟨22702490509465116099868421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15134993672976744066578947 22702490509465116099868421)
                  ·
                    refine ⟨4256716970524709268725329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22702490509465116099868421 4256716970524709268725329)
                    ·
                      refine ⟨3192537727893531951543997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256716970524709268725329 3192537727893531951543997)
                      ·
                        rfl

theorem cell23_6217445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6217445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217445 prefixEnd_6217445 := by exact prefixLift 6217445
  have htrace : WordTrace (prefixWord ++ tailWord_6217445) baseStart_6217445 baseEnd_6217445 := by
    simpa [prefixWord, tailWord_6217445, baseEnd_6217445] using wordTrace_append hprefix tailTrace_6217445
  have hstable : (prefixWord ++ tailWord_6217445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217445).length < 2 ^ (prefixWord ++ tailWord_6217445).sum := by decide
  have hdescent : baseEnd_6217445 < baseStart_6217445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217448 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6217448 : Nat := 118140960795 + 6217448 * 2 ^ 59
def prefixEnd_6217448 : Nat := 4983230072969 + 3 ^ 40 * 6217448 * 2
def baseEnd_6217448 : Nat := 3192539268335495439806483

theorem tailTrace_6217448 : CollatzResearch.WordTrace tailWord_6217448 prefixEnd_6217448 3192539268335495439806483 := by
  unfold tailWord_6217448
  simp only [CollatzResearch.WordTrace]
  refine ⟨113384479189627613212434499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151179305586170150949912665 113384479189627613212434499)
  ·
    refine ⟨170076718784441419818651749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113384479189627613212434499 170076718784441419818651749)
    ·
      refine ⟨31889384772082766215997203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170076718784441419818651749 31889384772082766215997203)
      ·
        refine ⟨47834077158124149323995805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31889384772082766215997203 47834077158124149323995805)
        ·
          refine ⟨17937778934296555996498427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47834077158124149323995805 17937778934296555996498427)
          ·
            refine ⟨26906668401444833994747641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17937778934296555996498427 26906668401444833994747641)
            ·
              refine ⟨20180001301083625496060731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26906668401444833994747641 20180001301083625496060731)
              ·
                refine ⟨30270001951625438244091097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20180001301083625496060731 30270001951625438244091097)
                ·
                  refine ⟨22702501463719078683068323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30270001951625438244091097 22702501463719078683068323)
                  ·
                    refine ⟨34053752195578618024602485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22702501463719078683068323 34053752195578618024602485)
                    ·
                      refine ⟨3192539268335495439806483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34053752195578618024602485 3192539268335495439806483)
                      ·
                        rfl

theorem cell23_6217448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6217448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217448 prefixEnd_6217448 := by exact prefixLift 6217448
  have htrace : WordTrace (prefixWord ++ tailWord_6217448) baseStart_6217448 baseEnd_6217448 := by
    simpa [prefixWord, tailWord_6217448, baseEnd_6217448] using wordTrace_append hprefix tailTrace_6217448
  have hstable : (prefixWord ++ tailWord_6217448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217448).length < 2 ^ (prefixWord ++ tailWord_6217448).sum := by decide
  have hdescent : baseEnd_6217448 < baseStart_6217448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217458 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6217458 : Nat := 118140960795 + 6217458 * 2 ^ 59
def prefixEnd_6217458 : Nat := 4983230072969 + 3 ^ 40 * 6217458 * 2
def baseEnd_6217458 : Nat := 3192544403142040400681437

theorem tailTrace_6217458 : CollatzResearch.WordTrace tailWord_6217458 prefixEnd_6217458 3192544403142040400681437 := by
  unfold tailWord_6217458
  simp only [CollatzResearch.WordTrace]
  refine ⟨56692330777304749533183257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151179548739479332088488685 56692330777304749533183257)
  ·
    refine ⟨42519248082978562149887443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56692330777304749533183257 42519248082978562149887443)
    ·
      refine ⟨63778872124467843224831165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42519248082978562149887443 63778872124467843224831165)
      ·
        refine ⟨23917077046675441209311687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63778872124467843224831165 23917077046675441209311687)
        ·
          refine ⟨35875615570013161813967531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23917077046675441209311687 35875615570013161813967531)
          ·
            refine ⟨53813423355019742720951297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35875615570013161813967531 53813423355019742720951297)
            ·
              refine ⟨40360067516264807040713473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53813423355019742720951297 40360067516264807040713473)
              ·
                refine ⟨30270050637198605280535105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40360067516264807040713473 30270050637198605280535105)
                ·
                  refine ⟨22702537977898953960401329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30270050637198605280535105 22702537977898953960401329)
                  ·
                    refine ⟨17026903483424215470300997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22702537977898953960401329 17026903483424215470300997)
                    ·
                      refine ⟨3192544403142040400681437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17026903483424215470300997 3192544403142040400681437)
                      ·
                        rfl

theorem cell23_6217458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6217458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217458 prefixEnd_6217458 := by exact prefixLift 6217458
  have htrace : WordTrace (prefixWord ++ tailWord_6217458) baseStart_6217458 baseEnd_6217458 := by
    simpa [prefixWord, tailWord_6217458, baseEnd_6217458] using wordTrace_append hprefix tailTrace_6217458
  have hstable : (prefixWord ++ tailWord_6217458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217458).length < 2 ^ (prefixWord ++ tailWord_6217458).sum := by decide
  have hdescent : baseEnd_6217458 < baseStart_6217458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217481 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_6217481 : Nat := 118140960795 + 6217481 * 2 ^ 59
def prefixEnd_6217481 : Nat := 4983230072969 + 3 ^ 40 * 6217481 * 2
def baseEnd_6217481 : Nat := 1064185404399031270231277

theorem tailTrace_6217481 : CollatzResearch.WordTrace tailWord_6217481 prefixEnd_6217481 1064185404399031270231277 := by
  unfold tailWord_6217481
  simp only [CollatzResearch.WordTrace]
  refine ⟨226770161988135673060820297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151180107992090448707213531 226770161988135673060820297)
  ·
    refine ⟨170077621491101754795615223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226770161988135673060820297 170077621491101754795615223)
    ·
      refine ⟨255116432236652632193422835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170077621491101754795615223 255116432236652632193422835)
      ·
        refine ⟨382674648354978948290134253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255116432236652632193422835 382674648354978948290134253)
        ·
          refine ⟨143502993133117105608800345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382674648354978948290134253 143502993133117105608800345)
          ·
            refine ⟨107627244849837829206600259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143502993133117105608800345 107627244849837829206600259)
            ·
              refine ⟨161440867274756743809900389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107627244849837829206600259 161440867274756743809900389)
              ·
                refine ⟨30270162614016889464356323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161440867274756743809900389 30270162614016889464356323)
                ·
                  refine ⟨45405243921025334196534485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30270162614016889464356323 45405243921025334196534485)
                  ·
                    refine ⟨1064185404399031270231277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45405243921025334196534485 1064185404399031270231277)
                    ·
                      rfl

theorem cell23_6217481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_6217481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217481 prefixEnd_6217481 := by exact prefixLift 6217481
  have htrace : WordTrace (prefixWord ++ tailWord_6217481) baseStart_6217481 baseEnd_6217481 := by
    simpa [prefixWord, tailWord_6217481, baseEnd_6217481] using wordTrace_append hprefix tailTrace_6217481
  have hstable : (prefixWord ++ tailWord_6217481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217481).length < 2 ^ (prefixWord ++ tailWord_6217481).sum := by decide
  have hdescent : baseEnd_6217481 < baseStart_6217481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217491 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_6217491 : Nat := 118140960795 + 6217491 * 2 ^ 59
def prefixEnd_6217491 : Nat := 4983230072969 + 3 ^ 40 * 6217491 * 2
def baseEnd_6217491 : Nat := 3192561348003638771568785

theorem tailTrace_6217491 : CollatzResearch.WordTrace tailWord_6217491 prefixEnd_6217491 3192561348003638771568785 := by
  unfold tailWord_6217491
  simp only [CollatzResearch.WordTrace]
  refine ⟨226770526718099444768684327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151180351145399629845789551 226770526718099444768684327)
  ·
    refine ⟨340155790077149167153026491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226770526718099444768684327 340155790077149167153026491)
    ·
      refine ⟨510233685115723750729539737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340155790077149167153026491 510233685115723750729539737)
      ·
        refine ⟨382675263836792813047154803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510233685115723750729539737 382675263836792813047154803)
        ·
          refine ⟨574012895755189219570732205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382675263836792813047154803 574012895755189219570732205)
          ·
            refine ⟨215254835908195957339024577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574012895755189219570732205 215254835908195957339024577)
            ·
              refine ⟨161441126931146968004268433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215254835908195957339024577 161441126931146968004268433)
              ·
                refine ⟨121080845198360226003201325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161441126931146968004268433 121080845198360226003201325)
                ·
                  refine ⟨45405316949385084751200497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121080845198360226003201325 45405316949385084751200497)
                  ·
                    refine ⟨34053987712038813563400373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45405316949385084751200497 34053987712038813563400373)
                    ·
                      refine ⟨3192561348003638771568785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34053987712038813563400373 3192561348003638771568785)
                      ·
                        rfl

theorem cell23_6217491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_6217491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217491 prefixEnd_6217491 := by exact prefixLift 6217491
  have htrace : WordTrace (prefixWord ++ tailWord_6217491) baseStart_6217491 baseEnd_6217491 := by
    simpa [prefixWord, tailWord_6217491, baseEnd_6217491] using wordTrace_append hprefix tailTrace_6217491
  have hstable : (prefixWord ++ tailWord_6217491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217491).length < 2 ^ (prefixWord ++ tailWord_6217491).sum := by decide
  have hdescent : baseEnd_6217491 < baseStart_6217491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217498 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_6217498 : Nat := 118140960795 + 6217498 * 2 ^ 59
def prefixEnd_6217498 : Nat := 4983230072969 + 3 ^ 40 * 6217498 * 2
def baseEnd_6217498 : Nat := 1064188314122740081393751

theorem tailTrace_6217498 : CollatzResearch.WordTrace tailWord_6217498 prefixEnd_6217498 1064188314122740081393751 := by
  unfold tailWord_6217498
  simp only [CollatzResearch.WordTrace]
  refine ⟨56692695507268521241047287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151180521352716056642792765 56692695507268521241047287)
  ·
    refine ⟨85039043260902781861570931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56692695507268521241047287 85039043260902781861570931)
    ·
      refine ⟨127558564891354172792356397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85039043260902781861570931 127558564891354172792356397)
      ·
        refine ⟨47834461834257814797133649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127558564891354172792356397 47834461834257814797133649)
        ·
          refine ⟨35875846375693361097850237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47834461834257814797133649 35875846375693361097850237)
          ·
            refine ⟨13453442390885010411693839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35875846375693361097850237 13453442390885010411693839)
            ·
              refine ⟨20180163586327515617540759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13453442390885010411693839 20180163586327515617540759)
              ·
                refine ⟨30270245379491273426311139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20180163586327515617540759 30270245379491273426311139)
                ·
                  refine ⟨45405368069236910139466709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30270245379491273426311139 45405368069236910139466709)
                  ·
                    refine ⟨1064188314122740081393751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45405368069236910139466709 1064188314122740081393751)
                    ·
                      rfl

theorem cell23_6217498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_6217498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217498 prefixEnd_6217498 := by exact prefixLift 6217498
  have htrace : WordTrace (prefixWord ++ tailWord_6217498) baseStart_6217498 baseEnd_6217498 := by
    simpa [prefixWord, tailWord_6217498, baseEnd_6217498] using wordTrace_append hprefix tailTrace_6217498
  have hstable : (prefixWord ++ tailWord_6217498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217498).length < 2 ^ (prefixWord ++ tailWord_6217498).sum := by decide
  have hdescent : baseEnd_6217498 < baseStart_6217498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217551 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_6217551 : Nat := 118140960795 + 6217551 * 2 ^ 59
def prefixEnd_6217551 : Nat := 4983230072969 + 3 ^ 40 * 6217551 * 2
def baseEnd_6217551 : Nat := 3192592156842908536818509

theorem tailTrace_6217551 : CollatzResearch.WordTrace tailWord_6217551 prefixEnd_6217551 3192592156842908536818509 := by
  unfold tailWord_6217551
  simp only [CollatzResearch.WordTrace]
  refine ⟨226772715097882075015868507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151181810065254716677245671 226772715097882075015868507)
  ·
    refine ⟨340159072646823112523802761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226772715097882075015868507 340159072646823112523802761)
    ·
      refine ⟨255119304485117334392852071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340159072646823112523802761 255119304485117334392852071)
      ·
        refine ⟨382678956727676001589278107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255119304485117334392852071 382678956727676001589278107)
        ·
          refine ⟨574018435091514002383917161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382678956727676001589278107 574018435091514002383917161)
          ·
            refine ⟨430513826318635501787937871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574018435091514002383917161 430513826318635501787937871)
            ·
              refine ⟨645770739477953252681906807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430513826318635501787937871 645770739477953252681906807)
              ·
                refine ⟨968656109216929879022860211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645770739477953252681906807 968656109216929879022860211)
                ·
                  refine ⟨1452984163825394818534290317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968656109216929879022860211 1452984163825394818534290317)
                  ·
                    refine ⟨544869061434523056950358869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1452984163825394818534290317 544869061434523056950358869)
                    ·
                      refine ⟨3192592156842908536818509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 544869061434523056950358869 3192592156842908536818509)
                      ·
                        rfl

theorem cell23_6217551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_6217551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217551 prefixEnd_6217551 := by exact prefixLift 6217551
  have htrace : WordTrace (prefixWord ++ tailWord_6217551) baseStart_6217551 baseEnd_6217551 := by
    simpa [prefixWord, tailWord_6217551, baseEnd_6217551] using wordTrace_append hprefix tailTrace_6217551
  have hstable : (prefixWord ++ tailWord_6217551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217551).length < 2 ^ (prefixWord ++ tailWord_6217551).sum := by decide
  have hdescent : baseEnd_6217551 < baseStart_6217551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217572 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_6217572 : Nat := 118140960795 + 6217572 * 2 ^ 59
def prefixEnd_6217572 : Nat := 4983230072969 + 3 ^ 40 * 6217572 * 2
def baseEnd_6217572 : Nat := 3192602939936652954655913

theorem tailTrace_6217572 : CollatzResearch.WordTrace tailWord_6217572 prefixEnd_6217572 3192602939936652954655913 := by
  unfold tailWord_6217572
  simp only [CollatzResearch.WordTrace]
  refine ⟨113386740515402997801191485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151182320687203997068255313 113386740515402997801191485)
  ·
    refine ⟨42520027693276124175446807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113386740515402997801191485 42520027693276124175446807)
    ·
      refine ⟨63780041539914186263170211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42520027693276124175446807 63780041539914186263170211)
      ·
        refine ⟨95670062309871279394755317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63780041539914186263170211 95670062309871279394755317)
        ·
          refine ⟨8969068341550432443258311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95670062309871279394755317 8969068341550432443258311)
          ·
            refine ⟨13453602512325648664887467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969068341550432443258311 13453602512325648664887467)
            ·
              refine ⟨20180403768488472997331201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13453602512325648664887467 20180403768488472997331201)
              ·
                refine ⟨15135302826366354747998401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20180403768488472997331201 15135302826366354747998401)
                ·
                  refine ⟨11351477119774766060998801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15135302826366354747998401 11351477119774766060998801)
                  ·
                    refine ⟨8513607839831074545749101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11351477119774766060998801 8513607839831074545749101)
                    ·
                      refine ⟨3192602939936652954655913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8513607839831074545749101 3192602939936652954655913)
                      ·
                        rfl

theorem cell23_6217572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_6217572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217572 prefixEnd_6217572 := by exact prefixLift 6217572
  have htrace : WordTrace (prefixWord ++ tailWord_6217572) baseStart_6217572 baseEnd_6217572 := by
    simpa [prefixWord, tailWord_6217572, baseEnd_6217572] using wordTrace_append hprefix tailTrace_6217572
  have hstable : (prefixWord ++ tailWord_6217572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217572).length < 2 ^ (prefixWord ++ tailWord_6217572).sum := by decide
  have hdescent : baseEnd_6217572 < baseStart_6217572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217595 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 6, 3, 2]
def baseStart_6217595 : Nat := 118140960795 + 6217595 * 2 ^ 59
def prefixEnd_6217595 : Nat := 4983230072969 + 3 ^ 40 * 6217595 * 2
def baseEnd_6217595 : Nat := 3192614749991706364668307

theorem tailTrace_6217595 : CollatzResearch.WordTrace tailWord_6217595 prefixEnd_6217595 3192614749991706364668307 := by
  unfold tailWord_6217595
  simp only [CollatzResearch.WordTrace]
  refine ⟨226774319909722670530470239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151182879939815113686980159 226774319909722670530470239)
  ·
    refine ⟨340161479864584005795705359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226774319909722670530470239 340161479864584005795705359)
    ·
      refine ⟨510242219796876008693558039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340161479864584005795705359 510242219796876008693558039)
      ·
        refine ⟨765363329695314013040337059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510242219796876008693558039 765363329695314013040337059)
        ·
          refine ⟨1148044994542971019560505589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765363329695314013040337059 1148044994542971019560505589)
          ·
            refine ⟨107629218238403533083797399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1148044994542971019560505589 107629218238403533083797399)
            ·
              refine ⟨161443827357605299625696099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107629218238403533083797399 161443827357605299625696099)
              ·
                refine ⟨242165741036407949438544149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161443827357605299625696099 242165741036407949438544149)
                ·
                  refine ⟨11351519111081622629931757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 242165741036407949438544149 11351519111081622629931757)
                  ·
                    refine ⟨4256819666655608486224409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11351519111081622629931757 4256819666655608486224409)
                    ·
                      refine ⟨3192614749991706364668307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256819666655608486224409 3192614749991706364668307)
                      ·
                        rfl

theorem cell23_6217595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 3, 2].length) (baseStart_6217595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217595 prefixEnd_6217595 := by exact prefixLift 6217595
  have htrace : WordTrace (prefixWord ++ tailWord_6217595) baseStart_6217595 baseEnd_6217595 := by
    simpa [prefixWord, tailWord_6217595, baseEnd_6217595] using wordTrace_append hprefix tailTrace_6217595
  have hstable : (prefixWord ++ tailWord_6217595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217595).length < 2 ^ (prefixWord ++ tailWord_6217595).sum := by decide
  have hdescent : baseEnd_6217595 < baseStart_6217595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217625 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_6217625 : Nat := 118140960795 + 6217625 * 2 ^ 59
def prefixEnd_6217625 : Nat := 4983230072969 + 3 ^ 40 * 6217625 * 2
def baseEnd_6217625 : Nat := 3192630154411341247293169

theorem tailTrace_6217625 : CollatzResearch.WordTrace tailWord_6217625 prefixEnd_6217625 3192630154411341247293169 := by
  unfold tailWord_6217625
  simp only [CollatzResearch.WordTrace]
  refine ⟨226775414099613985654062329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151183609399742657102708219 226775414099613985654062329)
  ·
    refine ⟨170081560574710489240546747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226775414099613985654062329 170081560574710489240546747)
    ·
      refine ⟨255122340862065733860820121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170081560574710489240546747 255122340862065733860820121)
      ·
        refine ⟨191341755646549300395615091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255122340862065733860820121 191341755646549300395615091)
        ·
          refine ⟨287012633469823950593422637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191341755646549300395615091 287012633469823950593422637)
          ·
            refine ⟨107629737551183981472533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287012633469823950593422637 107629737551183981472533489)
            ·
              refine ⟨80722303163387986104400117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107629737551183981472533489 80722303163387986104400117)
              ·
                refine ⟨7567715921567623697287511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80722303163387986104400117 7567715921567623697287511)
                ·
                  refine ⟨11351573882351435545931267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7567715921567623697287511 11351573882351435545931267)
                  ·
                    refine ⟨17027360823527153318896901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11351573882351435545931267 17027360823527153318896901)
                    ·
                      refine ⟨3192630154411341247293169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17027360823527153318896901 3192630154411341247293169)
                      ·
                        rfl

theorem cell23_6217625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_6217625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217625 prefixEnd_6217625 := by exact prefixLift 6217625
  have htrace : WordTrace (prefixWord ++ tailWord_6217625) baseStart_6217625 baseEnd_6217625 := by
    simpa [prefixWord, tailWord_6217625, baseEnd_6217625] using wordTrace_append hprefix tailTrace_6217625
  have hstable : (prefixWord ++ tailWord_6217625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217625).length < 2 ^ (prefixWord ++ tailWord_6217625).sum := by decide
  have hdescent : baseEnd_6217625 < baseStart_6217625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217630 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6217630 : Nat := 118140960795 + 6217630 * 2 ^ 59
def prefixEnd_6217630 : Nat := 4983230072969 + 3 ^ 40 * 6217630 * 2
def baseEnd_6217630 : Nat := 1064210907271537909243549

theorem tailTrace_6217630 : CollatzResearch.WordTrace tailWord_6217630 prefixEnd_6217630 1064210907271537909243549 := by
  unfold tailWord_6217630
  simp only [CollatzResearch.WordTrace]
  refine ⟨28346949558074483938499293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151183730976397247671996229 28346949558074483938499293)
  ·
    refine ⟨10630106084277931476937235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28346949558074483938499293 10630106084277931476937235)
    ·
      refine ⟨15945159126416897215405853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10630106084277931476937235 15945159126416897215405853)
      ·
        refine ⟨5979434672406336455777195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15945159126416897215405853 5979434672406336455777195)
        ·
          refine ⟨8969152008609504683665793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979434672406336455777195 8969152008609504683665793)
          ·
            refine ⟨6726864006457128512749345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969152008609504683665793 6726864006457128512749345)
            ·
              refine ⟨5045148004842846384562009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6726864006457128512749345 5045148004842846384562009)
              ·
                refine ⟨3783861003632134788421507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045148004842846384562009 3783861003632134788421507)
                ·
                  refine ⟨5675791505448202182632261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783861003632134788421507 5675791505448202182632261)
                  ·
                    refine ⟨1064210907271537909243549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5675791505448202182632261 1064210907271537909243549)
                    ·
                      rfl

theorem cell23_6217630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6217630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217630 prefixEnd_6217630 := by exact prefixLift 6217630
  have htrace : WordTrace (prefixWord ++ tailWord_6217630) baseStart_6217630 baseEnd_6217630 := by
    simpa [prefixWord, tailWord_6217630, baseEnd_6217630] using wordTrace_append hprefix tailTrace_6217630
  have hstable : (prefixWord ++ tailWord_6217630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217630).length < 2 ^ (prefixWord ++ tailWord_6217630).sum := by decide
  have hdescent : baseEnd_6217630 < baseStart_6217630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217636 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_6217636 : Nat := 118140960795 + 6217636 * 2 ^ 59
def prefixEnd_6217636 : Nat := 4983230072969 + 3 ^ 40 * 6217636 * 2
def baseEnd_6217636 : Nat := 3192635802698540704255619

theorem tailTrace_6217636 : CollatzResearch.WordTrace tailWord_6217636 prefixEnd_6217636 3192635802698540704255619 := by
  unfold tailWord_6217636
  simp only [CollatzResearch.WordTrace]
  refine ⟨113387907651287067266356381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151183876868382756355141841 113387907651287067266356381)
  ·
    refine ⟨42520465369232650224883643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113387907651287067266356381 42520465369232650224883643)
    ·
      refine ⟨63780698053848975337325465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42520465369232650224883643 63780698053848975337325465)
      ·
        refine ⟨47835523540386731502994099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63780698053848975337325465 47835523540386731502994099)
        ·
          refine ⟨71753285310580097254491149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47835523540386731502994099 71753285310580097254491149)
          ·
            refine ⟨26907481991467536470434181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71753285310580097254491149 26907481991467536470434181)
            ·
              refine ⟨5045152873400163088206409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26907481991467536470434181 5045152873400163088206409)
              ·
                refine ⟨3783864655050122316154807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045152873400163088206409 3783864655050122316154807)
                ·
                  refine ⟨5675796982575183474232211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783864655050122316154807 5675796982575183474232211)
                  ·
                    refine ⟨8513695473862775211348317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5675796982575183474232211 8513695473862775211348317)
                    ·
                      refine ⟨3192635802698540704255619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8513695473862775211348317 3192635802698540704255619)
                      ·
                        rfl

theorem cell23_6217636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_6217636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217636 prefixEnd_6217636 := by exact prefixLift 6217636
  have htrace : WordTrace (prefixWord ++ tailWord_6217636) baseStart_6217636 baseEnd_6217636 := by
    simpa [prefixWord, tailWord_6217636, baseEnd_6217636] using wordTrace_append hprefix tailTrace_6217636
  have hstable : (prefixWord ++ tailWord_6217636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217636).length < 2 ^ (prefixWord ++ tailWord_6217636).sum := by decide
  have hdescent : baseEnd_6217636 < baseStart_6217636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217662 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_6217662 : Nat := 118140960795 + 6217662 * 2 ^ 59
def prefixEnd_6217662 : Nat := 4983230072969 + 3 ^ 40 * 6217662 * 2
def baseEnd_6217662 : Nat := 3192649153195557602530499

theorem tailTrace_6217662 : CollatzResearch.WordTrace tailWord_6217662 prefixEnd_6217662 3192649153195557602530499 := by
  unfold tailWord_6217662
  simp only [CollatzResearch.WordTrace]
  refine ⟨28347095450059992621644905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151184509066986627315439493 28347095450059992621644905)
  ·
    refine ⟨21260321587544994466233679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28347095450059992621644905 21260321587544994466233679)
    ·
      refine ⟨31890482381317491699350519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21260321587544994466233679 31890482381317491699350519)
      ·
        refine ⟨47835723571976237549025779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31890482381317491699350519 47835723571976237549025779)
        ·
          refine ⟨71753585357964356323538669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47835723571976237549025779 71753585357964356323538669)
          ·
            refine ⟨26907594509236633621327001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71753585357964356323538669 26907594509236633621327001)
            ·
              refine ⟨20180695881927475215995251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26907594509236633621327001 20180695881927475215995251)
              ·
                refine ⟨30271043822891212823992877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20180695881927475215995251 30271043822891212823992877)
                ·
                  refine ⟨11351641433584204808997329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30271043822891212823992877 11351641433584204808997329)
                  ·
                    refine ⟨8513731075188153606747997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11351641433584204808997329 8513731075188153606747997)
                    ·
                      refine ⟨3192649153195557602530499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8513731075188153606747997 3192649153195557602530499)
                      ·
                        rfl

theorem cell23_6217662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_6217662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217662 prefixEnd_6217662 := by exact prefixLift 6217662
  have htrace : WordTrace (prefixWord ++ tailWord_6217662) baseStart_6217662 baseEnd_6217662 := by
    simpa [prefixWord, tailWord_6217662, baseEnd_6217662] using wordTrace_append hprefix tailTrace_6217662
  have hstable : (prefixWord ++ tailWord_6217662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217662).length < 2 ^ (prefixWord ++ tailWord_6217662).sum := by decide
  have hdescent : baseEnd_6217662 < baseStart_6217662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217675 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3]
def baseStart_6217675 : Nat := 118140960795 + 6217675 * 2 ^ 59
def prefixEnd_6217675 : Nat := 4983230072969 + 3 ^ 40 * 6217675 * 2
def baseEnd_6217675 : Nat := 3192655828444066051667939

theorem tailTrace_6217675 : CollatzResearch.WordTrace tailWord_6217675 prefixEnd_6217675 3192655828444066051667939 := by
  unfold tailWord_6217675
  simp only [CollatzResearch.WordTrace]
  refine ⟨226777237749432844193382479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151184825166288562795588319 226777237749432844193382479)
  ·
    refine ⟨340165856624149266290073719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226777237749432844193382479 340165856624149266290073719)
    ·
      refine ⟨510248784936223899435110579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340165856624149266290073719 510248784936223899435110579)
      ·
        refine ⟨765373177404335849152665869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510248784936223899435110579 765373177404335849152665869)
        ·
          refine ⟨287014941526625943432249701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765373177404335849152665869 287014941526625943432249701)
          ·
            refine ⟨53815301536242364393546819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287014941526625943432249701 53815301536242364393546819)
            ·
              refine ⟨80722952304363546590320229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53815301536242364393546819 80722952304363546590320229)
              ·
                refine ⟨15135553557068164985685043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80722952304363546590320229 15135553557068164985685043)
                ·
                  refine ⟨22703330335602247478527565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15135553557068164985685043 22703330335602247478527565)
                  ·
                    refine ⟨8513748875850842804447837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22703330335602247478527565 8513748875850842804447837)
                    ·
                      refine ⟨3192655828444066051667939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8513748875850842804447837 3192655828444066051667939)
                      ·
                        rfl

theorem cell23_6217675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3].length) (baseStart_6217675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217675 prefixEnd_6217675 := by exact prefixLift 6217675
  have htrace : WordTrace (prefixWord ++ tailWord_6217675) baseStart_6217675 baseEnd_6217675 := by
    simpa [prefixWord, tailWord_6217675, baseEnd_6217675] using wordTrace_append hprefix tailTrace_6217675
  have hstable : (prefixWord ++ tailWord_6217675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217675).length < 2 ^ (prefixWord ++ tailWord_6217675).sum := by decide
  have hdescent : baseEnd_6217675 < baseStart_6217675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217676 : List Nat := [2, 2, 1, 4, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6217676 : Nat := 118140960795 + 6217676 * 2 ^ 59
def prefixEnd_6217676 : Nat := 4983230072969 + 3 ^ 40 * 6217676 * 2
def baseEnd_6217676 : Nat := 3192656341924720547755435

theorem tailTrace_6217676 : CollatzResearch.WordTrace tailWord_6217676 prefixEnd_6217676 3192656341924720547755435 := by
  unfold tailWord_6217676
  simp only [CollatzResearch.WordTrace]
  refine ⟨113388637111214610682084441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151184849481619480909445921 113388637111214610682084441)
  ·
    refine ⟨85041477833410958011563331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113388637111214610682084441 85041477833410958011563331)
    ·
      refine ⟨127562216750116437017344997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85041477833410958011563331 127562216750116437017344997)
      ·
        refine ⟨23917915640646831940752187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127562216750116437017344997 23917915640646831940752187)
        ·
          refine ⟨35876873460970247911128281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23917915640646831940752187 35876873460970247911128281)
          ·
            refine ⟨26907655095727685933346211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35876873460970247911128281 26907655095727685933346211)
            ·
              refine ⟨40361482643591528900019317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26907655095727685933346211 40361482643591528900019317)
              ·
                refine ⟨3783888997836705834376811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40361482643591528900019317 3783888997836705834376811)
                ·
                  refine ⟨5675833496755058751565217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3783888997836705834376811 5675833496755058751565217)
                  ·
                    refine ⟨4256875122566294063673913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5675833496755058751565217 4256875122566294063673913)
                    ·
                      refine ⟨3192656341924720547755435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4256875122566294063673913 3192656341924720547755435)
                      ·
                        rfl

theorem cell23_6217676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6217676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217676 prefixEnd_6217676 := by exact prefixLift 6217676
  have htrace : WordTrace (prefixWord ++ tailWord_6217676) baseStart_6217676 baseEnd_6217676 := by
    simpa [prefixWord, tailWord_6217676, baseEnd_6217676] using wordTrace_append hprefix tailTrace_6217676
  have hstable : (prefixWord ++ tailWord_6217676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217676).length < 2 ^ (prefixWord ++ tailWord_6217676).sum := by decide
  have hdescent : baseEnd_6217676 < baseStart_6217676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217735 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6217735 : Nat := 118140960795 + 6217735 * 2 ^ 59
def prefixEnd_6217735 : Nat := 4983230072969 + 3 ^ 40 * 6217735 * 2
def baseEnd_6217735 : Nat := 3192686637283335816917663

theorem tailTrace_6217735 : CollatzResearch.WordTrace tailWord_6217735 prefixEnd_6217735 3192686637283335816917663 := by
  unfold tailWord_6217735
  simp only [CollatzResearch.WordTrace]
  refine ⟨226779426129215474440566659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151186284086143649627044439 226779426129215474440566659)
  ·
    refine ⟨340169139193823211660849989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226779426129215474440566659 340169139193823211660849989)
    ·
      refine ⟨63781713598841852186409373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340169139193823211660849989 63781713598841852186409373)
      ·
        refine ⟨23918142599565694569903515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63781713598841852186409373 23918142599565694569903515)
        ·
          refine ⟨35877213899348541854855273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23918142599565694569903515 35877213899348541854855273)
          ·
            refine ⟨26907910424511406391141455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35877213899348541854855273 26907910424511406391141455)
            ·
              refine ⟨40361865636767109586712183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26907910424511406391141455 40361865636767109586712183)
              ·
                refine ⟨60542798455150664380068275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40361865636767109586712183 60542798455150664380068275)
                ·
                  refine ⟨90814197682725996570102413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60542798455150664380068275 90814197682725996570102413)
                  ·
                    refine ⟨34055324131022248713788405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90814197682725996570102413 34055324131022248713788405)
                    ·
                      refine ⟨3192686637283335816917663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34055324131022248713788405 3192686637283335816917663)
                      ·
                        rfl

theorem cell23_6217735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6217735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217735 prefixEnd_6217735 := by exact prefixLift 6217735
  have htrace : WordTrace (prefixWord ++ tailWord_6217735) baseStart_6217735 baseEnd_6217735 := by
    simpa [prefixWord, tailWord_6217735, baseEnd_6217735] using wordTrace_append hprefix tailTrace_6217735
  have hstable : (prefixWord ++ tailWord_6217735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217735).length < 2 ^ (prefixWord ++ tailWord_6217735).sum := by decide
  have hdescent : baseEnd_6217735 < baseStart_6217735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217806 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_6217806 : Nat := 118140960795 + 6217806 * 2 ^ 59
def prefixEnd_6217806 : Nat := 4983230072969 + 3 ^ 40 * 6217806 * 2
def baseEnd_6217806 : Nat := 354747010489978337681093

theorem tailTrace_6217806 : CollatzResearch.WordTrace tailWord_6217806 prefixEnd_6217806 354747010489978337681093 := by
  unfold tailWord_6217806
  simp only [CollatzResearch.WordTrace]
  refine ⟨28347751963994781695800159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151188010474638835710934181 28347751963994781695800159)
  ·
    refine ⟨42521627945992172543700239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28347751963994781695800159 42521627945992172543700239)
    ·
      refine ⟨63782441918988258815550359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42521627945992172543700239 63782441918988258815550359)
      ·
        refine ⟨95673662878482388223325539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63782441918988258815550359 95673662878482388223325539)
        ·
          refine ⟨143510494317723582334988309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95673662878482388223325539 143510494317723582334988309)
          ·
            refine ⟨6727054421143292921952577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143510494317723582334988309 6727054421143292921952577)
            ·
              refine ⟨5045290815857469691464433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727054421143292921952577 5045290815857469691464433)
              ·
                refine ⟨3783968111893102268598325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045290815857469691464433 3783968111893102268598325)
                ·
                  refine ⟨354747010489978337681093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3783968111893102268598325 354747010489978337681093)
                  ·
                    rfl

theorem cell23_6217806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_6217806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217806 prefixEnd_6217806 := by exact prefixLift 6217806
  have htrace : WordTrace (prefixWord ++ tailWord_6217806) baseStart_6217806 baseEnd_6217806 := by
    simpa [prefixWord, tailWord_6217806, baseEnd_6217806] using wordTrace_append hprefix tailTrace_6217806
  have hstable : (prefixWord ++ tailWord_6217806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217806).length < 2 ^ (prefixWord ++ tailWord_6217806).sum := by decide
  have hdescent : baseEnd_6217806 < baseStart_6217806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217839 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_6217839 : Nat := 118140960795 + 6217839 * 2 ^ 59
def prefixEnd_6217839 : Nat := 4983230072969 + 3 ^ 40 * 6217839 * 2
def baseEnd_6217839 : Nat := 3192740039271403410017185

theorem tailTrace_6217839 : CollatzResearch.WordTrace tailWord_6217839 prefixEnd_6217839 3192740039271403410017185 := by
  unfold tailWord_6217839
  simp only [CollatzResearch.WordTrace]
  refine ⟨226783219320838700202352571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151188812880559133468235047 226783219320838700202352571)
  ·
    refine ⟨340174828981258050303528857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226783219320838700202352571 340174828981258050303528857)
    ·
      refine ⟨255131121735943537727646643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340174828981258050303528857 255131121735943537727646643)
      ·
        refine ⟨382696682603915306591469965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255131121735943537727646643 382696682603915306591469965)
        ·
          refine ⟨143511255976468239971801237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382696682603915306591469965 143511255976468239971801237)
          ·
            refine ⟨6727090123896948748678183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143511255976468239971801237 6727090123896948748678183)
            ·
              refine ⟨10090635185845423123017275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727090123896948748678183 10090635185845423123017275)
              ·
                refine ⟨15135952778768134684525913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10090635185845423123017275 15135952778768134684525913)
                ·
                  refine ⟨11351964584076101013394435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15135952778768134684525913 11351964584076101013394435)
                  ·
                    refine ⟨17027946876114151520091653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11351964584076101013394435 17027946876114151520091653)
                    ·
                      refine ⟨3192740039271403410017185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17027946876114151520091653 3192740039271403410017185)
                      ·
                        rfl

theorem cell23_6217839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_6217839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217839 prefixEnd_6217839 := by exact prefixLift 6217839
  have htrace : WordTrace (prefixWord ++ tailWord_6217839) baseStart_6217839 baseEnd_6217839 := by
    simpa [prefixWord, tailWord_6217839, baseEnd_6217839] using wordTrace_append hprefix tailTrace_6217839
  have hstable : (prefixWord ++ tailWord_6217839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217839).length < 2 ^ (prefixWord ++ tailWord_6217839).sum := by decide
  have hdescent : baseEnd_6217839 < baseStart_6217839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217865 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_6217865 : Nat := 118140960795 + 6217865 * 2 ^ 59
def prefixEnd_6217865 : Nat := 4983230072969 + 3 ^ 40 * 6217865 * 2
def baseEnd_6217865 : Nat := 3192753389768420308292065

theorem tailTrace_6217865 : CollatzResearch.WordTrace tailWord_6217865 prefixEnd_6217865 3192753389768420308292065 := by
  unfold tailWord_6217865
  simp only [CollatzResearch.WordTrace]
  refine ⟨226784167618744506642799049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151189445079163004428532699 226784167618744506642799049)
  ·
    refine ⟨170088125714058379982099287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226784167618744506642799049 170088125714058379982099287)
    ·
      refine ⟨255132188571087569973148931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170088125714058379982099287 255132188571087569973148931)
      ·
        refine ⟨382698282856631354959723397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255132188571087569973148931 382698282856631354959723397)
        ·
          refine ⟨71755928035618379054948137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382698282856631354959723397 71755928035618379054948137)
          ·
            refine ⟨53816946026713784291211103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71755928035618379054948137 53816946026713784291211103)
            ·
              refine ⟨80725419040070676436816655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53816946026713784291211103 80725419040070676436816655)
              ·
                refine ⟨121088128560106014655224983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80725419040070676436816655 121088128560106014655224983)
                ·
                  refine ⟨181632192840159021982837475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121088128560106014655224983 181632192840159021982837475)
                  ·
                    refine ⟨272448289260238532974256213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181632192840159021982837475 272448289260238532974256213)
                    ·
                      refine ⟨3192753389768420308292065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 272448289260238532974256213 3192753389768420308292065)
                      ·
                        rfl

theorem cell23_6217865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_6217865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217865 prefixEnd_6217865 := by exact prefixLift 6217865
  have htrace : WordTrace (prefixWord ++ tailWord_6217865) baseStart_6217865 baseEnd_6217865 := by
    simpa [prefixWord, tailWord_6217865, baseEnd_6217865] using wordTrace_append hprefix tailTrace_6217865
  have hstable : (prefixWord ++ tailWord_6217865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217865).length < 2 ^ (prefixWord ++ tailWord_6217865).sum := by decide
  have hdescent : baseEnd_6217865 < baseStart_6217865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217866 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_6217866 : Nat := 118140960795 + 6217866 * 2 ^ 59
def prefixEnd_6217866 : Nat := 4983230072969 + 3 ^ 40 * 6217866 * 2
def baseEnd_6217866 : Nat := 1064251301083024934793187

theorem tailTrace_6217866 : CollatzResearch.WordTrace tailWord_6217866 prefixEnd_6217866 1064251301083024934793187 := by
  unfold tailWord_6217866
  simp only [CollatzResearch.WordTrace]
  refine ⟨56696051022935220953396363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151189469394493922542390301 56696051022935220953396363)
  ·
    refine ⟨85044076534402831430094545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56696051022935220953396363 85044076534402831430094545)
    ·
      refine ⟨63783057400802123572570909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85044076534402831430094545 63783057400802123572570909)
      ·
        refine ⟨23918646525300796339714091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63783057400802123572570909 23918646525300796339714091)
        ·
          refine ⟨35877969787951194509571137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23918646525300796339714091 35877969787951194509571137)
          ·
            refine ⟨26908477340963395882178353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35877969787951194509571137 26908477340963395882178353)
            ·
              refine ⟨20181358005722546911633765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26908477340963395882178353 20181358005722546911633765)
              ·
                refine ⟨3784004626072977545931331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20181358005722546911633765 3784004626072977545931331)
                ·
                  refine ⟨5676006939109466318896997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784004626072977545931331 5676006939109466318896997)
                  ·
                    refine ⟨1064251301083024934793187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676006939109466318896997 1064251301083024934793187)
                    ·
                      rfl

theorem cell23_6217866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_6217866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217866 prefixEnd_6217866 := by exact prefixLift 6217866
  have htrace : WordTrace (prefixWord ++ tailWord_6217866) baseStart_6217866 baseEnd_6217866 := by
    simpa [prefixWord, tailWord_6217866, baseEnd_6217866] using wordTrace_append hprefix tailTrace_6217866
  have hstable : (prefixWord ++ tailWord_6217866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217866).length < 2 ^ (prefixWord ++ tailWord_6217866).sum := by decide
  have hdescent : baseEnd_6217866 < baseStart_6217866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217946 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2]
def baseStart_6217946 : Nat := 118140960795 + 6217946 * 2 ^ 59
def prefixEnd_6217946 : Nat := 4983230072969 + 3 ^ 40 * 6217946 * 2
def baseEnd_6217946 : Nat := 3192794981701434491379193

theorem tailTrace_6217946 : CollatzResearch.WordTrace tailWord_6217946 prefixEnd_6217946 3192794981701434491379193 := by
  unfold tailWord_6217946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56696780482862764369124423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151191414620967371650998461 56696780482862764369124423)
  ·
    refine ⟨85045170724294146553686635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56696780482862764369124423 85045170724294146553686635)
    ·
      refine ⟨127567756086441219830529953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85045170724294146553686635 127567756086441219830529953)
      ·
        refine ⟨95675817064830914872897465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127567756086441219830529953 95675817064830914872897465)
        ·
          refine ⟨71756862798623186154673099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95675817064830914872897465 71756862798623186154673099)
          ·
            refine ⟨107635294197934779232009649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71756862798623186154673099 107635294197934779232009649)
            ·
              refine ⟨80726470648451084424007237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107635294197934779232009649 80726470648451084424007237)
              ·
                refine ⟨15136213246584578329501357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80726470648451084424007237 15136213246584578329501357)
                ·
                  refine ⟨5676079967469216873563009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15136213246584578329501357 5676079967469216873563009)
                  ·
                    refine ⟨4257059975601912655172257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676079967469216873563009 4257059975601912655172257)
                    ·
                      refine ⟨3192794981701434491379193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257059975601912655172257 3192794981701434491379193)
                      ·
                        rfl

theorem cell23_6217946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_6217946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217946 prefixEnd_6217946 := by exact prefixLift 6217946
  have htrace : WordTrace (prefixWord ++ tailWord_6217946) baseStart_6217946 baseEnd_6217946 := by
    simpa [prefixWord, tailWord_6217946, baseEnd_6217946] using wordTrace_append hprefix tailTrace_6217946
  have hstable : (prefixWord ++ tailWord_6217946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217946).length < 2 ^ (prefixWord ++ tailWord_6217946).sum := by decide
  have hdescent : baseEnd_6217946 < baseStart_6217946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217959 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6217959 : Nat := 118140960795 + 6217959 * 2 ^ 59
def prefixEnd_6217959 : Nat := 4983230072969 + 3 ^ 40 * 6217959 * 2
def baseEnd_6217959 : Nat := 3192801656949942940516633

theorem tailTrace_6217959 : CollatzResearch.WordTrace tailWord_6217959 prefixEnd_6217959 3192801656949942940516633 := by
  unfold tailWord_6217959
  simp only [CollatzResearch.WordTrace]
  refine ⟨226787596080403960696720931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151191730720269307131147287 226787596080403960696720931)
  ·
    refine ⟨340181394120605941045081397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226787596080403960696720931 340181394120605941045081397)
    ·
      refine ⟨31892005698806806972976381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340181394120605941045081397 31892005698806806972976381)
      ·
        refine ⟨11959502137052552614866143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31892005698806806972976381 11959502137052552614866143)
        ·
          refine ⟨17939253205578828922299215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11959502137052552614866143 17939253205578828922299215)
          ·
            refine ⟨26908879808368243383448823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17939253205578828922299215 26908879808368243383448823)
            ·
              refine ⟨40363319712552365075173235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26908879808368243383448823 40363319712552365075173235)
              ·
                refine ⟨60544979568828547612759853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40363319712552365075173235 60544979568828547612759853)
                ·
                  refine ⟨22704367338310705354784945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60544979568828547612759853 22704367338310705354784945)
                  ·
                    refine ⟨17028275503733029016088709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22704367338310705354784945 17028275503733029016088709)
                    ·
                      refine ⟨3192801656949942940516633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17028275503733029016088709 3192801656949942940516633)
                      ·
                        rfl

theorem cell23_6217959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6217959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217959 prefixEnd_6217959 := by exact prefixLift 6217959
  have htrace : WordTrace (prefixWord ++ tailWord_6217959) baseStart_6217959 baseEnd_6217959 := by
    simpa [prefixWord, tailWord_6217959, baseEnd_6217959] using wordTrace_append hprefix tailTrace_6217959
  have hstable : (prefixWord ++ tailWord_6217959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217959).length < 2 ^ (prefixWord ++ tailWord_6217959).sum := by decide
  have hdescent : baseEnd_6217959 < baseStart_6217959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217963 : List Nat := [1, 1, 1, 1, 2, 5, 2, 5, 1, 2, 2]
def baseStart_6217963 : Nat := 118140960795 + 6217963 * 2 ^ 59
def prefixEnd_6217963 : Nat := 4983230072969 + 3 ^ 40 * 6217963 * 2
def baseEnd_6217963 : Nat := 3192803710872560924866615

theorem tailTrace_6217963 : CollatzResearch.WordTrace tailWord_6217963 prefixEnd_6217963 3192803710872560924866615 := by
  unfold tailWord_6217963
  simp only [CollatzResearch.WordTrace]
  refine ⟨226787741972389469379866543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151191827981592979586577695 226787741972389469379866543)
  ·
    refine ⟨340181612958584204069799815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226787741972389469379866543 340181612958584204069799815)
    ·
      refine ⟨510272419437876306104699723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340181612958584204069799815 510272419437876306104699723)
      ·
        refine ⟨765408629156814459157049585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510272419437876306104699723 765408629156814459157049585)
        ·
          refine ⟨574056471867610844367787189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765408629156814459157049585 574056471867610844367787189)
          ·
            refine ⟨53817794237588516659480049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 574056471867610844367787189 53817794237588516659480049)
            ·
              refine ⟨40363345678191387494610037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53817794237588516659480049 40363345678191387494610037)
              ·
                refine ⟨3784063657330442577619691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40363345678191387494610037 3784063657330442577619691)
                ·
                  refine ⟨5676095485995663866429537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784063657330442577619691 5676095485995663866429537)
                  ·
                    refine ⟨4257071614496747899822153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676095485995663866429537 4257071614496747899822153)
                    ·
                      refine ⟨3192803710872560924866615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257071614496747899822153 3192803710872560924866615)
                      ·
                        rfl

theorem cell23_6217963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 1, 2, 2].length) (baseStart_6217963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217963 prefixEnd_6217963 := by exact prefixLift 6217963
  have htrace : WordTrace (prefixWord ++ tailWord_6217963) baseStart_6217963 baseEnd_6217963 := by
    simpa [prefixWord, tailWord_6217963, baseEnd_6217963] using wordTrace_append hprefix tailTrace_6217963
  have hstable : (prefixWord ++ tailWord_6217963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217963).length < 2 ^ (prefixWord ++ tailWord_6217963).sum := by decide
  have hdescent : baseEnd_6217963 < baseStart_6217963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217980 : List Nat := [2, 2, 2, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_6217980 : Nat := 118140960795 + 6217980 * 2 ^ 59
def prefixEnd_6217980 : Nat := 4983230072969 + 3 ^ 40 * 6217980 * 2
def baseEnd_6217980 : Nat := 3192812440043687358354037

theorem tailTrace_6217980 : CollatzResearch.WordTrace tailWord_6217980 prefixEnd_6217980 3192812440043687358354037 := by
  unfold tailWord_6217980
  simp only [CollatzResearch.WordTrace]
  refine ⟨113394181006663940641617697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151192241342218587522156929 113394181006663940641617697)
  ·
    refine ⟨85045635754997955481213273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113394181006663940641617697 85045635754997955481213273)
    ·
      refine ⟨63784226816248466610909955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85045635754997955481213273 63784226816248466610909955)
      ·
        refine ⟨95676340224372699916364933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63784226816248466610909955 95676340224372699916364933)
        ·
          refine ⟨17939313792069881234318425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95676340224372699916364933 17939313792069881234318425)
          ·
            refine ⟨13454485344052410925738819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17939313792069881234318425 13454485344052410925738819)
            ·
              refine ⟨20181728016078616388608229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13454485344052410925738819 20181728016078616388608229)
              ·
                refine ⟨3784074003014740572864043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20181728016078616388608229 3784074003014740572864043)
                ·
                  refine ⟨5676111004522110859296065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784074003014740572864043 5676111004522110859296065)
                  ·
                    refine ⟨4257083253391583144472049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676111004522110859296065 4257083253391583144472049)
                    ·
                      refine ⟨3192812440043687358354037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257083253391583144472049 3192812440043687358354037)
                      ·
                        rfl

theorem cell23_6217980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_6217980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217980 prefixEnd_6217980 := by exact prefixLift 6217980
  have htrace : WordTrace (prefixWord ++ tailWord_6217980) baseStart_6217980 baseEnd_6217980 := by
    simpa [prefixWord, tailWord_6217980, baseEnd_6217980] using wordTrace_append hprefix tailTrace_6217980
  have hstable : (prefixWord ++ tailWord_6217980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217980).length < 2 ^ (prefixWord ++ tailWord_6217980).sum := by decide
  have hdescent : baseEnd_6217980 < baseStart_6217980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217986 : List Nat := [3, 4, 1, 1, 2, 3, 1, 8]
def baseStart_6217986 : Nat := 118140960795 + 6217986 * 2 ^ 59
def prefixEnd_6217986 : Nat := 4983230072969 + 3 ^ 40 * 6217986 * 2
def baseEnd_6217986 : Nat := 118252426701022753143667

theorem tailTrace_6217986 : CollatzResearch.WordTrace tailWord_6217986 prefixEnd_6217986 118252426701022753143667 := by
  unfold tailWord_6217986
  simp only [CollatzResearch.WordTrace]
  refine ⟨56697145212826536076988453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151192387234204096205302541 56697145212826536076988453)
  ·
    refine ⟨10630714727404975514435335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56697145212826536076988453 10630714727404975514435335)
    ·
      refine ⟨15946072091107463271653003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10630714727404975514435335 15946072091107463271653003)
      ·
        refine ⟨23919108136661194907479505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15946072091107463271653003 23919108136661194907479505)
        ·
          refine ⟨17939331102495896180609629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23919108136661194907479505 17939331102495896180609629)
          ·
            refine ⟨6727249163435961067728611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17939331102495896180609629 6727249163435961067728611)
            ·
              refine ⟨10090873745153941601592917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727249163435961067728611 10090873745153941601592917)
              ·
                refine ⟨118252426701022753143667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10090873745153941601592917 118252426701022753143667)
                ·
                  rfl

theorem cell23_6217986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_6217986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217986 prefixEnd_6217986 := by exact prefixLift 6217986
  have htrace : WordTrace (prefixWord ++ tailWord_6217986) baseStart_6217986 baseEnd_6217986 := by
    simpa [prefixWord, tailWord_6217986, baseEnd_6217986] using wordTrace_append hprefix tailTrace_6217986
  have hstable : (prefixWord ++ tailWord_6217986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217986).length < 2 ^ (prefixWord ++ tailWord_6217986).sum := by decide
  have hdescent : baseEnd_6217986 < baseStart_6217986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6217996 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_6217996 : Nat := 118140960795 + 6217996 * 2 ^ 59
def prefixEnd_6217996 : Nat := 4983230072969 + 3 ^ 40 * 6217996 * 2
def baseEnd_6217996 : Nat := 3192820655734159295753963

theorem tailTrace_6217996 : CollatzResearch.WordTrace tailWord_6217996 prefixEnd_6217996 3192820655734159295753963 := by
  unfold tailWord_6217996
  simp only [CollatzResearch.WordTrace]
  refine ⟨113394472790634958007908921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151192630387513277343878561 113394472790634958007908921)
  ·
    refine ⟨85045854592976218505931691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113394472790634958007908921 85045854592976218505931691)
    ·
      refine ⟨127568781889464327758897537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85045854592976218505931691 127568781889464327758897537)
      ·
        refine ⟨95676586417098245819173153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127568781889464327758897537 95676586417098245819173153)
        ·
          refine ⟨71757439812823684364379865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95676586417098245819173153 71757439812823684364379865)
          ·
            refine ⟨53818079859617763273284899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71757439812823684364379865 53818079859617763273284899)
            ·
              refine ⟨80727119789426644909927349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53818079859617763273284899 80727119789426644909927349)
              ·
                refine ⟨7568167480258747960305689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80727119789426644909927349 7568167480258747960305689)
                ·
                  refine ⟨5676125610194060970229267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7568167480258747960305689 5676125610194060970229267)
                  ·
                    refine ⟨8514188415291091455343901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5676125610194060970229267 8514188415291091455343901)
                    ·
                      refine ⟨3192820655734159295753963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514188415291091455343901 3192820655734159295753963)
                      ·
                        rfl

theorem cell23_6217996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_6217996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6217996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6217996 prefixEnd_6217996 := by exact prefixLift 6217996
  have htrace : WordTrace (prefixWord ++ tailWord_6217996) baseStart_6217996 baseEnd_6217996 := by
    simpa [prefixWord, tailWord_6217996, baseEnd_6217996] using wordTrace_append hprefix tailTrace_6217996
  have hstable : (prefixWord ++ tailWord_6217996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6217996).length < 2 ^ (prefixWord ++ tailWord_6217996).sum := by decide
  have hdescent : baseEnd_6217996 < baseStart_6217996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6217996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218012 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_6218012 : Nat := 118140960795 + 6218012 * 2 ^ 59
def prefixEnd_6218012 : Nat := 4983230072969 + 3 ^ 40 * 6218012 * 2
def baseEnd_6218012 : Nat := 1064276290474877077717963

theorem tailTrace_6218012 : CollatzResearch.WordTrace tailWord_6218012 prefixEnd_6218012 1064276290474877077717963 := by
  unfold tailWord_6218012
  simp only [CollatzResearch.WordTrace]
  refine ⟨113394764574605975374200145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151193019432807967165600193 113394764574605975374200145)
  ·
    refine ⟨85046073430954481530650109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113394764574605975374200145 85046073430954481530650109)
    ·
      refine ⟨31892277536607930573993791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85046073430954481530650109 31892277536607930573993791)
      ·
        refine ⟨47838416304911895860990687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31892277536607930573993791 47838416304911895860990687)
        ·
          refine ⟨71757624457367843791486031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47838416304911895860990687 71757624457367843791486031)
          ·
            refine ⟨107636436686051765687229047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71757624457367843791486031 107636436686051765687229047)
            ·
              refine ⟨161454655029077648530843571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107636436686051765687229047 161454655029077648530843571)
              ·
                refine ⟨242181982543616472796265357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161454655029077648530843571 242181982543616472796265357)
                ·
                  refine ⟨90818243453856177298599509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242181982543616472796265357 90818243453856177298599509)
                  ·
                    refine ⟨1064276290474877077717963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90818243453856177298599509 1064276290474877077717963)
                    ·
                      rfl

theorem cell23_6218012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_6218012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218012 prefixEnd_6218012 := by exact prefixLift 6218012
  have htrace : WordTrace (prefixWord ++ tailWord_6218012) baseStart_6218012 baseEnd_6218012 := by
    simpa [prefixWord, tailWord_6218012, baseEnd_6218012] using wordTrace_append hprefix tailTrace_6218012
  have hstable : (prefixWord ++ tailWord_6218012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218012).length < 2 ^ (prefixWord ++ tailWord_6218012).sum := by decide
  have hdescent : baseEnd_6218012 < baseStart_6218012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218014 : List Nat := [4, 3, 2, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6218014 : Nat := 118140960795 + 6218014 * 2 ^ 59
def prefixEnd_6218014 : Nat := 4983230072969 + 3 ^ 40 * 6218014 * 2
def baseEnd_6218014 : Nat := 3192829898385940225328881

theorem tailTrace_6218014 : CollatzResearch.WordTrace tailWord_6218014 prefixEnd_6218014 3192829898385940225328881 := by
  unfold tailWord_6218014
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348700261900588136246637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151193068063469803393315397 28348700261900588136246637)
  ·
    refine ⟨10630762598212720551092489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28348700261900588136246637 10630762598212720551092489)
    ·
      refine ⟨7973071948659540413319367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10630762598212720551092489 7973071948659540413319367)
      ·
        refine ⟨11959607922989310619979051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973071948659540413319367 11959607922989310619979051)
        ·
          refine ⟨17939411884483965929968577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11959607922989310619979051 17939411884483965929968577)
          ·
            refine ⟨13454558913362974447476433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17939411884483965929968577 13454558913362974447476433)
            ·
              refine ⟨10090919185022230835607325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13454558913362974447476433 10090919185022230835607325)
              ·
                refine ⟨3784094694383336563352747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10090919185022230835607325 3784094694383336563352747)
                ·
                  refine ⟨5676142041575004845029121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784094694383336563352747 5676142041575004845029121)
                  ·
                    refine ⟨4257106531181253633771841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676142041575004845029121 4257106531181253633771841)
                    ·
                      refine ⟨3192829898385940225328881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257106531181253633771841 3192829898385940225328881)
                      ·
                        rfl

theorem cell23_6218014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6218014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218014 prefixEnd_6218014 := by exact prefixLift 6218014
  have htrace : WordTrace (prefixWord ++ tailWord_6218014) baseStart_6218014 baseEnd_6218014 := by
    simpa [prefixWord, tailWord_6218014, baseEnd_6218014] using wordTrace_append hprefix tailTrace_6218014
  have hstable : (prefixWord ++ tailWord_6218014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218014).length < 2 ^ (prefixWord ++ tailWord_6218014).sum := by decide
  have hdescent : baseEnd_6218014 < baseStart_6218014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218030 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6218030 : Nat := 118140960795 + 6218030 * 2 ^ 59
def prefixEnd_6218030 : Nat := 4983230072969 + 3 ^ 40 * 6218030 * 2
def baseEnd_6218030 : Nat := 3192838114076412162728807

theorem tailTrace_6218030 : CollatzResearch.WordTrace tailWord_6218030 prefixEnd_6218030 3192838114076412162728807 := by
  unfold tailWord_6218030
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348773207893342477819443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151193457108764493215037029 28348773207893342477819443)
  ·
    refine ⟨42523159811840013716729165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28348773207893342477819443 42523159811840013716729165)
    ·
      refine ⟨15946184929440005143773437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42523159811840013716729165 15946184929440005143773437)
      ·
        refine ⟨5979819348540001928915039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15946184929440005143773437 5979819348540001928915039)
        ·
          refine ⟨8969729022810002893372559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979819348540001928915039 8969729022810002893372559)
          ·
            refine ⟨13454593534215004340058839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8969729022810002893372559 13454593534215004340058839)
            ·
              refine ⟨20181890301322506510088259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13454593534215004340058839 20181890301322506510088259)
              ·
                refine ⟨30272835451983759765132389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20181890301322506510088259 30272835451983759765132389)
                ·
                  refine ⟨5676156647246954955962323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30272835451983759765132389 5676156647246954955962323)
                  ·
                    refine ⟨8514234970870432433943485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5676156647246954955962323 8514234970870432433943485)
                    ·
                      refine ⟨3192838114076412162728807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514234970870432433943485 3192838114076412162728807)
                      ·
                        rfl

theorem cell23_6218030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6218030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218030 prefixEnd_6218030 := by exact prefixLift 6218030
  have htrace : WordTrace (prefixWord ++ tailWord_6218030) baseStart_6218030 baseEnd_6218030 := by
    simpa [prefixWord, tailWord_6218030, baseEnd_6218030] using wordTrace_append hprefix tailTrace_6218030
  have hstable : (prefixWord ++ tailWord_6218030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218030).length < 2 ^ (prefixWord ++ tailWord_6218030).sum := by decide
  have hdescent : baseEnd_6218030 < baseStart_6218030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218089 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_6218089 : Nat := 118140960795 + 6218089 * 2 ^ 59
def prefixEnd_6218089 : Nat := 4983230072969 + 3 ^ 40 * 6218089 * 2
def baseEnd_6218089 : Nat := 1064289469811675810630345

theorem tailTrace_6218089 : CollatzResearch.WordTrace tailWord_6218089 prefixEnd_6218089 1064289469811675810630345 := by
  unfold tailWord_6218089
  simp only [CollatzResearch.WordTrace]
  refine ⟨226792337569932992898953321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151194891713288661932635547 226792337569932992898953321)
  ·
    refine ⟨170094253177449744674214991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226792337569932992898953321 170094253177449744674214991)
    ·
      refine ⟨255141379766174617011322487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170094253177449744674214991 255141379766174617011322487)
      ·
        refine ⟨382712069649261925516983731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255141379766174617011322487 382712069649261925516983731)
        ·
          refine ⟨574068104473892888275475597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382712069649261925516983731 574068104473892888275475597)
          ·
            refine ⟨215275539177709833103303349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574068104473892888275475597 215275539177709833103303349)
            ·
              refine ⟨20182081797910296853434689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215275539177709833103303349 20182081797910296853434689)
              ·
                refine ⟨15136561348432722640076017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20182081797910296853434689 15136561348432722640076017)
                ·
                  refine ⟨11352421011324541980057013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15136561348432722640076017 11352421011324541980057013)
                  ·
                    refine ⟨1064289469811675810630345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11352421011324541980057013 1064289469811675810630345)
                    ·
                      rfl

theorem cell23_6218089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_6218089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218089 prefixEnd_6218089 := by exact prefixLift 6218089
  have htrace : WordTrace (prefixWord ++ tailWord_6218089) baseStart_6218089 baseEnd_6218089 := by
    simpa [prefixWord, tailWord_6218089, baseEnd_6218089] using wordTrace_append hprefix tailTrace_6218089
  have hstable : (prefixWord ++ tailWord_6218089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218089).length < 2 ^ (prefixWord ++ tailWord_6218089).sum := by decide
  have hdescent : baseEnd_6218089 < baseStart_6218089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218093 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 5]
def baseStart_6218093 : Nat := 118140960795 + 6218093 * 2 ^ 59
def prefixEnd_6218093 : Nat := 4983230072969 + 3 ^ 40 * 6218093 * 2
def baseEnd_6218093 : Nat := 354763384817516157360113

theorem tailTrace_6218093 : CollatzResearch.WordTrace tailWord_6218093 prefixEnd_6218093 354763384817516157360113 := by
  unfold tailWord_6218093
  simp only [CollatzResearch.WordTrace]
  refine ⟨226792483461918501582098933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151194988974612334388065955 226792483461918501582098933)
  ·
    refine ⟨21261795324554859523321775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226792483461918501582098933 21261795324554859523321775)
    ·
      refine ⟨31892692986832289284982663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21261795324554859523321775 31892692986832289284982663)
      ·
        refine ⟨47839039480248433927473995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31892692986832289284982663 47839039480248433927473995)
        ·
          refine ⟨71758559220372650891210993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47839039480248433927473995 71758559220372650891210993)
          ·
            refine ⟨53818919415279488168408245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71758559220372650891210993 53818919415279488168408245)
            ·
              refine ⟨5045523695182452015788273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53818919415279488168408245 5045523695182452015788273)
              ·
                refine ⟨3784142771386839011841205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045523695182452015788273 3784142771386839011841205)
                ·
                  refine ⟨354763384817516157360113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3784142771386839011841205 354763384817516157360113)
                  ·
                    rfl

theorem cell23_6218093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_6218093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218093 prefixEnd_6218093 := by exact prefixLift 6218093
  have htrace : WordTrace (prefixWord ++ tailWord_6218093) baseStart_6218093 baseEnd_6218093 := by
    simpa [prefixWord, tailWord_6218093, baseEnd_6218093] using wordTrace_append hprefix tailTrace_6218093
  have hstable : (prefixWord ++ tailWord_6218093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218093).length < 2 ^ (prefixWord ++ tailWord_6218093).sum := by decide
  have hdescent : baseEnd_6218093 < baseStart_6218093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218159 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_6218159 : Nat := 118140960795 + 6218159 * 2 ^ 59
def prefixEnd_6218159 : Nat := 4983230072969 + 3 ^ 40 * 6218159 * 2
def baseEnd_6218159 : Nat := 3192904353080842158015713

theorem tailTrace_6218159 : CollatzResearch.WordTrace tailWord_6218159 prefixEnd_6218159 3192904353080842158015713 := by
  unfold tailWord_6218159
  simp only [CollatzResearch.WordTrace]
  refine ⟨226794890679679394854001531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151196593786452929902667687 226794890679679394854001531)
  ·
    refine ⟨340192336019519092281002297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226794890679679394854001531 340192336019519092281002297)
    ·
      refine ⟨255144252014639319210751723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340192336019519092281002297 255144252014639319210751723)
      ·
        refine ⟨382716378021958978816127585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255144252014639319210751723 382716378021958978816127585)
        ·
          refine ⟨287037283516469234112095689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382716378021958978816127585 287037283516469234112095689)
          ·
            refine ⟨215277962637351925584071767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287037283516469234112095689 215277962637351925584071767)
            ·
              refine ⟨322916943956027888376107651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215277962637351925584071767 322916943956027888376107651)
              ·
                refine ⟨484375415934041832564161477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322916943956027888376107651 484375415934041832564161477)
                ·
                  refine ⟨90820390487632843605780277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484375415934041832564161477 90820390487632843605780277)
                  ·
                    refine ⟨8514411608215579088041901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90820390487632843605780277 8514411608215579088041901)
                    ·
                      refine ⟨3192904353080842158015713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514411608215579088041901 3192904353080842158015713)
                      ·
                        rfl

theorem cell23_6218159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_6218159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218159 prefixEnd_6218159 := by exact prefixLift 6218159
  have htrace : WordTrace (prefixWord ++ tailWord_6218159) baseStart_6218159 baseEnd_6218159 := by
    simpa [prefixWord, tailWord_6218159, baseEnd_6218159] using wordTrace_append hprefix tailTrace_6218159
  have hstable : (prefixWord ++ tailWord_6218159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218159).length < 2 ^ (prefixWord ++ tailWord_6218159).sum := by decide
  have hdescent : baseEnd_6218159 < baseStart_6218159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218239 : List Nat := [1, 1, 2, 2, 1, 2, 5, 9]
def baseStart_6218239 : Nat := 118140960795 + 6218239 * 2 ^ 59
def prefixEnd_6218239 : Nat := 4983230072969 + 3 ^ 40 * 6218239 * 2
def baseEnd_6218239 : Nat := 118257238204933401667235

theorem tailTrace_6218239 : CollatzResearch.WordTrace tailWord_6218239 prefixEnd_6218239 118257238204933401667235 := by
  unfold tailWord_6218239
  simp only [CollatzResearch.WordTrace]
  refine ⟨226797808519389568516913771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151198539012926379011275847 226797808519389568516913771)
  ·
    refine ⟨340196712779084352775370657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226797808519389568516913771 340196712779084352775370657)
    ·
      refine ⟨255147534584313264581527993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340196712779084352775370657 255147534584313264581527993)
      ·
        refine ⟨191360650938234948436145995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255147534584313264581527993 191360650938234948436145995)
        ·
          refine ⟨287040976407352422654218993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191360650938234948436145995 287040976407352422654218993)
          ·
            refine ⟨215280732305514316990664245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287040976407352422654218993 215280732305514316990664245)
            ·
              refine ⟨20182568653641967217874773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215280732305514316990664245 20182568653641967217874773)
              ·
                refine ⟨118257238204933401667235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20182568653641967217874773 118257238204933401667235)
                ·
                  rfl

theorem cell23_6218239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 9].length) (baseStart_6218239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218239 prefixEnd_6218239 := by exact prefixLift 6218239
  have htrace : WordTrace (prefixWord ++ tailWord_6218239) baseStart_6218239 baseEnd_6218239 := by
    simpa [prefixWord, tailWord_6218239, baseEnd_6218239] using wordTrace_append hprefix tailTrace_6218239
  have hstable : (prefixWord ++ tailWord_6218239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218239).length < 2 ^ (prefixWord ++ tailWord_6218239).sum := by decide
  have hdescent : baseEnd_6218239 < baseStart_6218239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218244 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6218244 : Nat := 118140960795 + 6218244 * 2 ^ 59
def prefixEnd_6218244 : Nat := 4983230072969 + 3 ^ 40 * 6218244 * 2
def baseEnd_6218244 : Nat := 3192947998936474325452823

theorem tailTrace_6218244 : CollatzResearch.WordTrace tailWord_6218244 prefixEnd_6218244 3192947998936474325452823 := by
  unfold tailWord_6218244
  simp only [CollatzResearch.WordTrace]
  refine ⟨113398995442185727185422893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151198660589580969580563857 113398995442185727185422893)
  ·
    refine ⟨42524623290819647694533585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113398995442185727185422893 42524623290819647694533585)
    ·
      refine ⟨31893467468114735770900189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42524623290819647694533585 31893467468114735770900189)
      ·
        refine ⟨11960050300543025914087571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31893467468114735770900189 11960050300543025914087571)
        ·
          refine ⟨17940075450814538871131357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960050300543025914087571 17940075450814538871131357)
          ·
            refine ⟨6727528294055452076674259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17940075450814538871131357 6727528294055452076674259)
            ·
              refine ⟨10091292441083178115011389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727528294055452076674259 10091292441083178115011389)
              ·
                refine ⟨3784234665406191793129271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091292441083178115011389 3784234665406191793129271)
                ·
                  refine ⟨5676351998109287689693907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784234665406191793129271 5676351998109287689693907)
                  ·
                    refine ⟨8514527997163931534540861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5676351998109287689693907 8514527997163931534540861)
                    ·
                      refine ⟨3192947998936474325452823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514527997163931534540861 3192947998936474325452823)
                      ·
                        rfl

theorem cell23_6218244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6218244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218244 prefixEnd_6218244 := by exact prefixLift 6218244
  have htrace : WordTrace (prefixWord ++ tailWord_6218244) baseStart_6218244 baseEnd_6218244 := by
    simpa [prefixWord, tailWord_6218244, baseEnd_6218244] using wordTrace_append hprefix tailTrace_6218244
  have hstable : (prefixWord ++ tailWord_6218244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218244).length < 2 ^ (prefixWord ++ tailWord_6218244).sum := by decide
  have hdescent : baseEnd_6218244 < baseStart_6218244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218260 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6218260 : Nat := 118140960795 + 6218260 * 2 ^ 59
def prefixEnd_6218260 : Nat := 4983230072969 + 3 ^ 40 * 6218260 * 2
def baseEnd_6218260 : Nat := 1064318738208982087617583

theorem tailTrace_6218260 : CollatzResearch.WordTrace tailWord_6218260 prefixEnd_6218260 1064318738208982087617583 := by
  unfold tailWord_6218260
  simp only [CollatzResearch.WordTrace]
  refine ⟨113399287226156744551714117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151199049634875659402285489 113399287226156744551714117)
  ·
    refine ⟨21262366354904389603446397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113399287226156744551714117 21262366354904389603446397)
    ·
      refine ⟨7973387383089146101292399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21262366354904389603446397 7973387383089146101292399)
      ·
        refine ⟨11960081074633719151938599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973387383089146101292399 11960081074633719151938599)
        ·
          refine ⟨17940121611950578727907899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960081074633719151938599 17940121611950578727907899)
          ·
            refine ⟨26910182417925868091861849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17940121611950578727907899 26910182417925868091861849)
            ·
              refine ⟨20182636813444401068896387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26910182417925868091861849 20182636813444401068896387)
              ·
                refine ⟨30273955220166601603344581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20182636813444401068896387 30273955220166601603344581)
                ·
                  refine ⟨5676366603781237800627109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30273955220166601603344581 5676366603781237800627109)
                  ·
                    refine ⟨1064318738208982087617583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676366603781237800627109 1064318738208982087617583)
                    ·
                      rfl

theorem cell23_6218260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6218260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218260 prefixEnd_6218260 := by exact prefixLift 6218260
  have htrace : WordTrace (prefixWord ++ tailWord_6218260) baseStart_6218260 baseEnd_6218260 := by
    simpa [prefixWord, tailWord_6218260, baseEnd_6218260] using wordTrace_append hprefix tailTrace_6218260
  have hstable : (prefixWord ++ tailWord_6218260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218260).length < 2 ^ (prefixWord ++ tailWord_6218260).sum := by decide
  have hdescent : baseEnd_6218260 < baseStart_6218260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218316 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_6218316 : Nat := 118140960795 + 6218316 * 2 ^ 59
def prefixEnd_6218316 : Nat := 4983230072969 + 3 ^ 40 * 6218316 * 2
def baseEnd_6218316 : Nat := 1064328323181199347917497

theorem tailTrace_6218316 : CollatzResearch.WordTrace tailWord_6218316 prefixEnd_6218316 1064328323181199347917497 := by
  unfold tailWord_6218316
  simp only [CollatzResearch.WordTrace]
  refine ⟨113400308470055305333733401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151200411293407073778311201 113400308470055305333733401)
  ·
    refine ⟨85050231352541479000300051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113400308470055305333733401 85050231352541479000300051)
    ·
      refine ⟨127575347028812218500450077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85050231352541479000300051 127575347028812218500450077)
      ·
        refine ⟨47840755135804581937668779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127575347028812218500450077 47840755135804581937668779)
        ·
          refine ⟨71761132703706872906503169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47840755135804581937668779 71761132703706872906503169)
          ·
            refine ⟨53820849527780154679877377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71761132703706872906503169 53820849527780154679877377)
            ·
              refine ⟨40365637145835116009908033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53820849527780154679877377 40365637145835116009908033)
              ·
                refine ⟨30274227859376337007431025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40365637145835116009908033 30274227859376337007431025)
                ·
                  refine ⟨22705670894532252755573269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30274227859376337007431025 22705670894532252755573269)
                  ·
                    refine ⟨1064328323181199347917497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22705670894532252755573269 1064328323181199347917497)
                    ·
                      rfl

theorem cell23_6218316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_6218316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218316 prefixEnd_6218316 := by exact prefixLift 6218316
  have htrace : WordTrace (prefixWord ++ tailWord_6218316) baseStart_6218316 baseEnd_6218316 := by
    simpa [prefixWord, tailWord_6218316, baseEnd_6218316] using wordTrace_append hprefix tailTrace_6218316
  have hstable : (prefixWord ++ tailWord_6218316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218316).length < 2 ^ (prefixWord ++ tailWord_6218316).sum := by decide
  have hdescent : baseEnd_6218316 < baseStart_6218316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218317 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_6218317 : Nat := 118140960795 + 6218317 * 2 ^ 59
def prefixEnd_6218317 : Nat := 4983230072969 + 3 ^ 40 * 6218317 * 2
def baseEnd_6218317 : Nat := 3192985483024252539839987

theorem tailTrace_6218317 : CollatzResearch.WordTrace tailWord_6218317 prefixEnd_6218317 3192985483024252539839987 := by
  unfold tailWord_6218317
  simp only [CollatzResearch.WordTrace]
  refine ⟨226800653413106987838253205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151200435608737991892168803 226800653413106987838253205)
  ·
    refine ⟨10631280628739390054918119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226800653413106987838253205 10631280628739390054918119)
    ·
      refine ⟨15946920943109085082377179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631280628739390054918119 15946920943109085082377179)
      ·
        refine ⟨23920381414663627623565769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15946920943109085082377179 23920381414663627623565769)
        ·
          refine ⟨17940286060997720717674327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23920381414663627623565769 17940286060997720717674327)
          ·
            refine ⟨26910429091496581076511491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17940286060997720717674327 26910429091496581076511491)
            ·
              refine ⟨40365643637244871614767237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26910429091496581076511491 40365643637244871614767237)
              ·
                refine ⟨7568558181983413427768857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40365643637244871614767237 7568558181983413427768857)
                ·
                  refine ⟨5676418636487560070826643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7568558181983413427768857 5676418636487560070826643)
                  ·
                    refine ⟨8514627954731340106239965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5676418636487560070826643 8514627954731340106239965)
                    ·
                      refine ⟨3192985483024252539839987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514627954731340106239965 3192985483024252539839987)
                      ·
                        rfl

theorem cell23_6218317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_6218317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218317 prefixEnd_6218317 := by exact prefixLift 6218317
  have htrace : WordTrace (prefixWord ++ tailWord_6218317) baseStart_6218317 baseEnd_6218317 := by
    simpa [prefixWord, tailWord_6218317, baseEnd_6218317] using wordTrace_append hprefix tailTrace_6218317
  have hstable : (prefixWord ++ tailWord_6218317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218317).length < 2 ^ (prefixWord ++ tailWord_6218317).sum := by decide
  have hdescent : baseEnd_6218317 < baseStart_6218317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218336 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_6218336 : Nat := 118140960795 + 6218336 * 2 ^ 59
def prefixEnd_6218336 : Nat := 4983230072969 + 3 ^ 40 * 6218336 * 2
def baseEnd_6218336 : Nat := 3192995239156687965502399

theorem tailTrace_6218336 : CollatzResearch.WordTrace tailWord_6218336 prefixEnd_6218336 3192995239156687965502399 := by
  unfold tailWord_6218336
  simp only [CollatzResearch.WordTrace]
  refine ⟨113400673200019077041597431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151200897600025436055463241 113400673200019077041597431)
  ·
    refine ⟨170101009800028615562396147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113400673200019077041597431 170101009800028615562396147)
    ·
      refine ⟨255151514700042923343594221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170101009800028615562396147 255151514700042923343594221)
      ·
        refine ⟨95681818012516096253847833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255151514700042923343594221 95681818012516096253847833)
        ·
          refine ⟨71761363509387072190385875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95681818012516096253847833 71761363509387072190385875)
          ·
            refine ⟨107642045264080608285578813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71761363509387072190385875 107642045264080608285578813)
            ·
              refine ⟨40365766974030228107092055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107642045264080608285578813 40365766974030228107092055)
              ·
                refine ⟨60548650461045342160638083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40365766974030228107092055 60548650461045342160638083)
                ·
                  refine ⟨90822975691568013240957125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60548650461045342160638083 90822975691568013240957125)
                  ·
                    refine ⟨17029307942169002482679461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90822975691568013240957125 17029307942169002482679461)
                    ·
                      refine ⟨3192995239156687965502399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17029307942169002482679461 3192995239156687965502399)
                      ·
                        rfl

theorem cell23_6218336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_6218336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218336 prefixEnd_6218336 := by exact prefixLift 6218336
  have htrace : WordTrace (prefixWord ++ tailWord_6218336) baseStart_6218336 baseEnd_6218336 := by
    simpa [prefixWord, tailWord_6218336, baseEnd_6218336] using wordTrace_append hprefix tailTrace_6218336
  have hstable : (prefixWord ++ tailWord_6218336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218336).length < 2 ^ (prefixWord ++ tailWord_6218336).sum := by decide
  have hdescent : baseEnd_6218336 < baseStart_6218336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218340 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_6218340 : Nat := 118140960795 + 6218340 * 2 ^ 59
def prefixEnd_6218340 : Nat := 4983230072969 + 3 ^ 40 * 6218340 * 2
def baseEnd_6218340 : Nat := 3192997293079305949852381

theorem tailTrace_6218340 : CollatzResearch.WordTrace tailWord_6218340 prefixEnd_6218340 3192997293079305949852381 := by
  unfold tailWord_6218340
  simp only [CollatzResearch.WordTrace]
  refine ⟨113400746146011831383170237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151200994861349108510893649 113400746146011831383170237)
  ·
    refine ⟨42525279804754436768688839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113400746146011831383170237 42525279804754436768688839)
    ·
      refine ⟨63787919707131655153033259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42525279804754436768688839 63787919707131655153033259)
      ·
        refine ⟨95681879560697482729549889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63787919707131655153033259 95681879560697482729549889)
        ·
          refine ⟨71761409670523112047162417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95681879560697482729549889 71761409670523112047162417)
          ·
            refine ⟨53821057252892334035371813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71761409670523112047162417 53821057252892334035371813)
            ·
              refine ⟨10091448234917312631632215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53821057252892334035371813 10091448234917312631632215)
              ·
                refine ⟨15137172352375968947448323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10091448234917312631632215 15137172352375968947448323)
                ·
                  refine ⟨22705758528563953421172485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137172352375968947448323 22705758528563953421172485)
                  ·
                    refine ⟨4257329724105741266469841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22705758528563953421172485 4257329724105741266469841)
                    ·
                      refine ⟨3192997293079305949852381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257329724105741266469841 3192997293079305949852381)
                      ·
                        rfl

theorem cell23_6218340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_6218340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218340 prefixEnd_6218340 := by exact prefixLift 6218340
  have htrace : WordTrace (prefixWord ++ tailWord_6218340) baseStart_6218340 baseEnd_6218340 := by
    simpa [prefixWord, tailWord_6218340, baseEnd_6218340] using wordTrace_append hprefix tailTrace_6218340
  have hstable : (prefixWord ++ tailWord_6218340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218340).length < 2 ^ (prefixWord ++ tailWord_6218340).sum := by decide
  have hdescent : baseEnd_6218340 < baseStart_6218340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218373 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_6218373 : Nat := 118140960795 + 6218373 * 2 ^ 59
def prefixEnd_6218373 : Nat := 4983230072969 + 3 ^ 40 * 6218373 * 2
def baseEnd_6218373 : Nat := 3193014237940904320739729

theorem tailTrace_6218373 : CollatzResearch.WordTrace tailWord_6218373 prefixEnd_6218373 3193014237940904320739729 := by
  unfold tailWord_6218373
  simp only [CollatzResearch.WordTrace]
  refine ⟨226802695900904109402291773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151201797267269406268194515 226802695900904109402291773)
  ·
    refine ⟨85051010962839041025859415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226802695900904109402291773 85051010962839041025859415)
    ·
      refine ⟨127576516444258561538789123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85051010962839041025859415 127576516444258561538789123)
      ·
        refine ⟨191364774666387842308183685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127576516444258561538789123 191364774666387842308183685)
        ·
          refine ⟨35880895249947720432784441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191364774666387842308183685 35880895249947720432784441)
          ·
            refine ⟨26910671437460790324588331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35880895249947720432784441 26910671437460790324588331)
            ·
              refine ⟨40366007156191185486882497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26910671437460790324588331 40366007156191185486882497)
              ·
                refine ⟨30274505367143389115161873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40366007156191185486882497 30274505367143389115161873)
                ·
                  refine ⟨22705879025357541836371405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30274505367143389115161873 22705879025357541836371405)
                  ·
                    refine ⟨8514704634509078188639277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22705879025357541836371405 8514704634509078188639277)
                    ·
                      refine ⟨3193014237940904320739729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514704634509078188639277 3193014237940904320739729)
                      ·
                        rfl

theorem cell23_6218373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_6218373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218373 prefixEnd_6218373 := by exact prefixLift 6218373
  have htrace : WordTrace (prefixWord ++ tailWord_6218373) baseStart_6218373 baseEnd_6218373 := by
    simpa [prefixWord, tailWord_6218373, baseEnd_6218373] using wordTrace_append hprefix tailTrace_6218373
  have hstable : (prefixWord ++ tailWord_6218373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218373).length < 2 ^ (prefixWord ++ tailWord_6218373).sum := by decide
  have hdescent : baseEnd_6218373 < baseStart_6218373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218414 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_6218414 : Nat := 118140960795 + 6218414 * 2 ^ 59
def prefixEnd_6218414 : Nat := 4983230072969 + 3 ^ 40 * 6218414 * 2
def baseEnd_6218414 : Nat := 354781698960859851147449

theorem tailTrace_6218414 : CollatzResearch.WordTrace tailWord_6218414 prefixEnd_6218414 354781698960859851147449 := by
  unfold tailWord_6218414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28350523911719446675566787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151202794195837048936356197 28350523911719446675566787)
  ·
    refine ⟨42525785867579170013350181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28350523911719446675566787 42525785867579170013350181)
    ·
      refine ⟨7973584850171094377503159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42525785867579170013350181 7973584850171094377503159)
      ·
        refine ⟨11960377275256641566254739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7973584850171094377503159 11960377275256641566254739)
        ·
          refine ⟨17940565912884962349382109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960377275256641566254739 17940565912884962349382109)
          ·
            refine ⟨6727712217331860881018291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17940565912884962349382109 6727712217331860881018291)
            ·
              refine ⟨10091568325997791321527437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727712217331860881018291 10091568325997791321527437)
              ·
                refine ⟨3784338122249171745572789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091568325997791321527437 3784338122249171745572789)
                ·
                  refine ⟨354781698960859851147449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3784338122249171745572789 354781698960859851147449)
                  ·
                    rfl

theorem cell23_6218414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_6218414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218414 prefixEnd_6218414 := by exact prefixLift 6218414
  have htrace : WordTrace (prefixWord ++ tailWord_6218414) baseStart_6218414 baseEnd_6218414 := by
    simpa [prefixWord, tailWord_6218414, baseEnd_6218414] using wordTrace_append hprefix tailTrace_6218414
  have hstable : (prefixWord ++ tailWord_6218414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218414).length < 2 ^ (prefixWord ++ tailWord_6218414).sum := by decide
  have hdescent : baseEnd_6218414 < baseStart_6218414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218416 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_6218416 : Nat := 118140960795 + 6218416 * 2 ^ 59
def prefixEnd_6218416 : Nat := 4983230072969 + 3 ^ 40 * 6218416 * 2
def baseEnd_6218416 : Nat := 3193036317609047652502031

theorem tailTrace_6218416 : CollatzResearch.WordTrace tailWord_6218416 prefixEnd_6218416 3193036317609047652502031 := by
  unfold tailWord_6218416
  simp only [CollatzResearch.WordTrace]
  refine ⟨113402132119874163873053551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151202842826498885164071401 113402132119874163873053551)
  ·
    refine ⟨170103198179811245809580327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113402132119874163873053551 170103198179811245809580327)
    ·
      refine ⟨255154797269716868714370491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170103198179811245809580327 255154797269716868714370491)
      ·
        refine ⟨382732195904575303071555737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255154797269716868714370491 382732195904575303071555737)
        ·
          refine ⟨287049146928431477303666803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382732195904575303071555737 287049146928431477303666803)
          ·
            refine ⟨430573720392647215955500205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287049146928431477303666803 430573720392647215955500205)
            ·
              refine ⟨161465145147242705983312577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430573720392647215955500205 161465145147242705983312577)
              ·
                refine ⟨121098858860432029487484433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161465145147242705983312577 121098858860432029487484433)
                ·
                  refine ⟨90824144145324022115613325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121098858860432029487484433 90824144145324022115613325)
                  ·
                    refine ⟨34059054054496508293354997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90824144145324022115613325 34059054054496508293354997)
                    ·
                      refine ⟨3193036317609047652502031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34059054054496508293354997 3193036317609047652502031)
                      ·
                        rfl

theorem cell23_6218416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_6218416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218416 prefixEnd_6218416 := by exact prefixLift 6218416
  have htrace : WordTrace (prefixWord ++ tailWord_6218416) baseStart_6218416 baseEnd_6218416 := by
    simpa [prefixWord, tailWord_6218416, baseEnd_6218416] using wordTrace_append hprefix tailTrace_6218416
  have hstable : (prefixWord ++ tailWord_6218416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218416).length < 2 ^ (prefixWord ++ tailWord_6218416).sum := by decide
  have hdescent : baseEnd_6218416 < baseStart_6218416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218430 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_6218430 : Nat := 118140960795 + 6218430 * 2 ^ 59
def prefixEnd_6218430 : Nat := 4983230072969 + 3 ^ 40 * 6218430 * 2
def baseEnd_6218430 : Nat := 3193043506338210597726967

theorem tailTrace_6218430 : CollatzResearch.WordTrace tailWord_6218430 prefixEnd_6218430 3193043506338210597726967 := by
  unfold tailWord_6218430
  simp only [CollatzResearch.WordTrace]
  refine ⟨28350596857712201017139593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151203183241131738758077829 28350596857712201017139593)
  ·
    refine ⟨21262947643284150762854695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28350596857712201017139593 21262947643284150762854695)
    ·
      refine ⟨31894421464926226144282043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21262947643284150762854695 31894421464926226144282043)
      ·
        refine ⟨47841632197389339216423065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31894421464926226144282043 47841632197389339216423065)
        ·
          refine ⟨35881224148042004412317299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47841632197389339216423065 35881224148042004412317299)
          ·
            refine ⟨53821836222063006618475949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35881224148042004412317299 53821836222063006618475949)
            ·
              refine ⟨20183188583273627481928481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53821836222063006618475949 20183188583273627481928481)
              ·
                refine ⟨15137391437455220611446361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20183188583273627481928481 15137391437455220611446361)
                ·
                  refine ⟨11353043578091415458584771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15137391437455220611446361 11353043578091415458584771)
                  ·
                    refine ⟨17029565367137123187877157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11353043578091415458584771 17029565367137123187877157)
                    ·
                      refine ⟨3193043506338210597726967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17029565367137123187877157 3193043506338210597726967)
                      ·
                        rfl

theorem cell23_6218430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_6218430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218430 prefixEnd_6218430 := by exact prefixLift 6218430
  have htrace : WordTrace (prefixWord ++ tailWord_6218430) baseStart_6218430 baseEnd_6218430 := by
    simpa [prefixWord, tailWord_6218430, baseEnd_6218430] using wordTrace_append hprefix tailTrace_6218430
  have hstable : (prefixWord ++ tailWord_6218430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218430).length < 2 ^ (prefixWord ++ tailWord_6218430).sum := by decide
  have hdescent : baseEnd_6218430 < baseStart_6218430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218440 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_6218440 : Nat := 118140960795 + 6218440 * 2 ^ 59
def prefixEnd_6218440 : Nat := 4983230072969 + 3 ^ 40 * 6218440 * 2
def baseEnd_6218440 : Nat := 1064349547048251852867307

theorem tailTrace_6218440 : CollatzResearch.WordTrace tailWord_6218440 prefixEnd_6218440 1064349547048251852867307 := by
  unfold tailWord_6218440
  simp only [CollatzResearch.WordTrace]
  refine ⟨113402569795830689922490387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151203426394440919896653849 113402569795830689922490387)
  ·
    refine ⟨170103854693746034883735581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113402569795830689922490387 170103854693746034883735581)
    ·
      refine ⟨63788945510154763081400843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170103854693746034883735581 63788945510154763081400843)
      ·
        refine ⟨95683418265232144622101265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63788945510154763081400843 95683418265232144622101265)
        ·
          refine ⟨71762563698924108466575949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95683418265232144622101265 71762563698924108466575949)
          ·
            refine ⟨26910961387096540674965981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71762563698924108466575949 26910961387096540674965981)
            ·
              refine ⟨10091610520161202753112243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26910961387096540674965981 10091610520161202753112243)
              ·
                refine ⟨15137415780241804129668365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10091610520161202753112243 15137415780241804129668365)
                ·
                  refine ⟨5676530917590676548625637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15137415780241804129668365 5676530917590676548625637)
                  ·
                    refine ⟨1064349547048251852867307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676530917590676548625637 1064349547048251852867307)
                    ·
                      rfl

theorem cell23_6218440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_6218440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218440 prefixEnd_6218440 := by exact prefixLift 6218440
  have htrace : WordTrace (prefixWord ++ tailWord_6218440) baseStart_6218440 baseEnd_6218440 := by
    simpa [prefixWord, tailWord_6218440, baseEnd_6218440] using wordTrace_append hprefix tailTrace_6218440
  have hstable : (prefixWord ++ tailWord_6218440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218440).length < 2 ^ (prefixWord ++ tailWord_6218440).sum := by decide
  have hdescent : baseEnd_6218440 < baseStart_6218440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218467 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6218467 : Nat := 118140960795 + 6218467 * 2 ^ 59
def prefixEnd_6218467 : Nat := 4983230072969 + 3 ^ 40 * 6218467 * 2
def baseEnd_6218467 : Nat := 3193062505122426952964297

theorem tailTrace_6218467 : CollatzResearch.WordTrace tailWord_6218467 prefixEnd_6218467 3193062505122426952964297 := by
  unfold tailWord_6218467
  simp only [CollatzResearch.WordTrace]
  refine ⟨226806124362563563456213655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151204082908375708970809103 226806124362563563456213655)
  ·
    refine ⟨340209186543845345184320483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226806124362563563456213655 340209186543845345184320483)
    ·
      refine ⟨510313779815768017776480725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340209186543845345184320483 510313779815768017776480725)
      ·
        refine ⟨11960479214432062916636267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 510313779815768017776480725 11960479214432062916636267)
        ·
          refine ⟨17940718821648094374954401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960479214432062916636267 17940718821648094374954401)
          ·
            refine ⟨13455539116236070781215801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17940718821648094374954401 13455539116236070781215801)
            ·
              refine ⟨10091654337177053085911851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13455539116236070781215801 10091654337177053085911851)
              ·
                refine ⟨15137481505765579628867777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10091654337177053085911851 15137481505765579628867777)
                ·
                  refine ⟨11353111129324184721650833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15137481505765579628867777 11353111129324184721650833)
                  ·
                    refine ⟨8514833346993138541238125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11353111129324184721650833 8514833346993138541238125)
                    ·
                      refine ⟨3193062505122426952964297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514833346993138541238125 3193062505122426952964297)
                      ·
                        rfl

theorem cell23_6218467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6218467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218467 prefixEnd_6218467 := by exact prefixLift 6218467
  have htrace : WordTrace (prefixWord ++ tailWord_6218467) baseStart_6218467 baseEnd_6218467 := by
    simpa [prefixWord, tailWord_6218467, baseEnd_6218467] using wordTrace_append hprefix tailTrace_6218467
  have hstable : (prefixWord ++ tailWord_6218467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218467).length < 2 ^ (prefixWord ++ tailWord_6218467).sum := by decide
  have hdescent : baseEnd_6218467 < baseStart_6218467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218513 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_6218513 : Nat := 118140960795 + 6218513 * 2 ^ 59
def prefixEnd_6218513 : Nat := 4983230072969 + 3 ^ 40 * 6218513 * 2
def baseEnd_6218513 : Nat := 1064362041744177924329695

theorem tailTrace_6218513 : CollatzResearch.WordTrace tailWord_6218513 prefixEnd_6218513 1064362041744177924329695 := by
  unfold tailWord_6218513
  simp only [CollatzResearch.WordTrace]
  refine ⟨226807802120396913312388193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151205201413597942208258795 226807802120396913312388193)
  ·
    refine ⟨170105851590297684984291145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226807802120396913312388193 170105851590297684984291145)
    ·
      refine ⟨127579388692723263738218359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170105851590297684984291145 127579388692723263738218359)
      ·
        refine ⟨191369083039084895607327539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127579388692723263738218359 191369083039084895607327539)
        ·
          refine ⟨287053624558627343410991309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191369083039084895607327539 287053624558627343410991309)
          ·
            refine ⟨107645109209485253779121741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287053624558627343410991309 107645109209485253779121741)
            ·
              refine ⟨40366915953556970167170653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107645109209485253779121741 40366915953556970167170653)
              ·
                refine ⟨15137593482583863812688995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40366915953556970167170653 15137593482583863812688995)
                ·
                  refine ⟨22706390223875795719033493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137593482583863812688995 22706390223875795719033493)
                  ·
                    refine ⟨1064362041744177924329695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22706390223875795719033493 1064362041744177924329695)
                    ·
                      rfl

theorem cell23_6218513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_6218513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218513 prefixEnd_6218513 := by exact prefixLift 6218513
  have htrace : WordTrace (prefixWord ++ tailWord_6218513) baseStart_6218513 baseEnd_6218513 := by
    simpa [prefixWord, tailWord_6218513, baseEnd_6218513] using wordTrace_append hprefix tailTrace_6218513
  have hstable : (prefixWord ++ tailWord_6218513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218513).length < 2 ^ (prefixWord ++ tailWord_6218513).sum := by decide
  have hdescent : baseEnd_6218513 < baseStart_6218513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218520 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6218520 : Nat := 118140960795 + 6218520 * 2 ^ 59
def prefixEnd_6218520 : Nat := 4983230072969 + 3 ^ 40 * 6218520 * 2
def baseEnd_6218520 : Nat := 3193089719597115245601553

theorem tailTrace_6218520 : CollatzResearch.WordTrace tailWord_6218520 prefixEnd_6218520 3193089719597115245601553 := by
  unfold tailWord_6218520
  simp only [CollatzResearch.WordTrace]
  refine ⟨113404028715685776753946507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151205371620914369005262009 113404028715685776753946507)
  ·
    refine ⟨170106043073528665130919761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113404028715685776753946507 170106043073528665130919761)
    ·
      refine ⟨127579532305146498848189821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170106043073528665130919761 127579532305146498848189821)
      ·
        refine ⟨47842324614429937068071183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127579532305146498848189821 47842324614429937068071183)
        ·
          refine ⟨71763486921644905602106775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47842324614429937068071183 71763486921644905602106775)
          ·
            refine ⟨107645230382467358403160163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71763486921644905602106775 107645230382467358403160163)
            ·
              refine ⟨161467845573701037604740245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107645230382467358403160163 161467845573701037604740245)
              ·
                refine ⟨7568805261267236137722199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161467845573701037604740245 7568805261267236137722199)
                ·
                  refine ⟨11353207891900854206583299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7568805261267236137722199 11353207891900854206583299)
                  ·
                    refine ⟨17029811837851281309874949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11353207891900854206583299 17029811837851281309874949)
                    ·
                      refine ⟨3193089719597115245601553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17029811837851281309874949 3193089719597115245601553)
                      ·
                        rfl

theorem cell23_6218520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6218520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218520 prefixEnd_6218520 := by exact prefixLift 6218520
  have htrace : WordTrace (prefixWord ++ tailWord_6218520) baseStart_6218520 baseEnd_6218520 := by
    simpa [prefixWord, tailWord_6218520, baseEnd_6218520] using wordTrace_append hprefix tailTrace_6218520
  have hstable : (prefixWord ++ tailWord_6218520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218520).length < 2 ^ (prefixWord ++ tailWord_6218520).sum := by decide
  have hdescent : baseEnd_6218520 < baseStart_6218520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218524 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6218524 : Nat := 118140960795 + 6218524 * 2 ^ 59
def prefixEnd_6218524 : Nat := 4983230072969 + 3 ^ 40 * 6218524 * 2
def baseEnd_6218524 : Nat := 3193091773519733229951535

theorem tailTrace_6218524 : CollatzResearch.WordTrace tailWord_6218524 prefixEnd_6218524 3193091773519733229951535 := by
  unfold tailWord_6218524
  simp only [CollatzResearch.WordTrace]
  refine ⟨113404101661678531095519313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151205468882238041460692417 113404101661678531095519313)
  ·
    refine ⟨85053076246258898321639485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113404101661678531095519313 85053076246258898321639485)
    ·
      refine ⟨31894903592347086870614807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85053076246258898321639485 31894903592347086870614807)
      ·
        refine ⟨47842355388520630305922211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31894903592347086870614807 47842355388520630305922211)
        ·
          refine ⟨71763533082780945458883317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47842355388520630305922211 71763533082780945458883317)
          ·
            refine ⟨6727831226510713636770311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71763533082780945458883317 6727831226510713636770311)
            ·
              refine ⟨10091746839766070455155467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727831226510713636770311 10091746839766070455155467)
              ·
                refine ⟨15137620259649105682733201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10091746839766070455155467 15137620259649105682733201)
                ·
                  refine ⟨11353215194736829262049901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15137620259649105682733201 11353215194736829262049901)
                  ·
                    refine ⟨4257455698026310973268713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11353215194736829262049901 4257455698026310973268713)
                    ·
                      refine ⟨3193091773519733229951535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257455698026310973268713 3193091773519733229951535)
                      ·
                        rfl

theorem cell23_6218524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6218524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218524 prefixEnd_6218524 := by exact prefixLift 6218524
  have htrace : WordTrace (prefixWord ++ tailWord_6218524) baseStart_6218524 baseEnd_6218524 := by
    simpa [prefixWord, tailWord_6218524, baseEnd_6218524] using wordTrace_append hprefix tailTrace_6218524
  have hstable : (prefixWord ++ tailWord_6218524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218524).length < 2 ^ (prefixWord ++ tailWord_6218524).sum := by decide
  have hdescent : baseEnd_6218524 < baseStart_6218524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218530 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6218530 : Nat := 118140960795 + 6218530 * 2 ^ 59
def prefixEnd_6218530 : Nat := 4983230072969 + 3 ^ 40 * 6218530 * 2
def baseEnd_6218530 : Nat := 1064364951467886735492169

theorem tailTrace_6218530 : CollatzResearch.WordTrace tailWord_6218530 prefixEnd_6218530 1064364951467886735492169 := by
  unfold tailWord_6218530
  simp only [CollatzResearch.WordTrace]
  refine ⟨56702105540333831303939261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151205614774223550143838029 56702105540333831303939261)
  ·
    refine ⟨21263289577625186738977223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56702105540333831303939261 21263289577625186738977223)
    ·
      refine ⟨31894934366437780108465835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21263289577625186738977223 31894934366437780108465835)
      ·
        refine ⟨47842401549656670162698753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31894934366437780108465835 47842401549656670162698753)
        ·
          refine ⟨35881801162242502622024065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47842401549656670162698753 35881801162242502622024065)
          ·
            refine ⟨26911350871681876966518049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35881801162242502622024065 26911350871681876966518049)
            ·
              refine ⟨20183513153761407724888537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26911350871681876966518049 20183513153761407724888537)
              ·
                refine ⟨15137634865321055793666403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20183513153761407724888537 15137634865321055793666403)
                ·
                  refine ⟨22706452297981583690499605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137634865321055793666403 22706452297981583690499605)
                  ·
                    refine ⟨1064364951467886735492169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22706452297981583690499605 1064364951467886735492169)
                    ·
                      rfl

theorem cell23_6218530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6218530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218530 prefixEnd_6218530 := by exact prefixLift 6218530
  have htrace : WordTrace (prefixWord ++ tailWord_6218530) baseStart_6218530 baseEnd_6218530 := by
    simpa [prefixWord, tailWord_6218530, baseEnd_6218530] using wordTrace_append hprefix tailTrace_6218530
  have hstable : (prefixWord ++ tailWord_6218530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218530).length < 2 ^ (prefixWord ++ tailWord_6218530).sum := by decide
  have hdescent : baseEnd_6218530 < baseStart_6218530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218547 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 2, 4]
def baseStart_6218547 : Nat := 118140960795 + 6218547 * 2 ^ 59
def prefixEnd_6218547 : Nat := 4983230072969 + 3 ^ 40 * 6218547 * 2
def baseEnd_6218547 : Nat := 1064367861191595546654643

theorem tailTrace_6218547 : CollatzResearch.WordTrace tailWord_6218547 prefixEnd_6218547 1064367861191595546654643 := by
  unfold tailWord_6218547
  simp only [CollatzResearch.WordTrace]
  refine ⟨226809042202273737119125895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151206028134849158079417263 226809042202273737119125895)
  ·
    refine ⟨340213563303410605678688843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226809042202273737119125895 340213563303410605678688843)
    ·
      refine ⟨510320344955115908518033265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340213563303410605678688843 510320344955115908518033265)
      ·
        refine ⟨382740258716336931388524949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510320344955115908518033265 382740258716336931388524949)
        ·
          refine ⟨17940949627328293658837107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382740258716336931388524949 17940949627328293658837107)
          ·
            refine ⟨26911424440992440488255661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17940949627328293658837107 26911424440992440488255661)
            ·
              refine ⟨10091784165372165183095873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26911424440992440488255661 10091784165372165183095873)
              ·
                refine ⟨7568838124029123887321905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10091784165372165183095873 7568838124029123887321905)
                ·
                  refine ⟨5676628593021842915491429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7568838124029123887321905 5676628593021842915491429)
                  ·
                    refine ⟨1064367861191595546654643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5676628593021842915491429 1064367861191595546654643)
                    ·
                      rfl

theorem cell23_6218547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 4].length) (baseStart_6218547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218547 prefixEnd_6218547 := by exact prefixLift 6218547
  have htrace : WordTrace (prefixWord ++ tailWord_6218547) baseStart_6218547 baseEnd_6218547 := by
    simpa [prefixWord, tailWord_6218547, baseEnd_6218547] using wordTrace_append hprefix tailTrace_6218547
  have hstable : (prefixWord ++ tailWord_6218547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218547).length < 2 ^ (prefixWord ++ tailWord_6218547).sum := by decide
  have hdescent : baseEnd_6218547 < baseStart_6218547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218557 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6218557 : Nat := 118140960795 + 6218557 * 2 ^ 59
def prefixEnd_6218557 : Nat := 4983230072969 + 3 ^ 40 * 6218557 * 2
def baseEnd_6218557 : Nat := 3193108718381331600838883

theorem tailTrace_6218557 : CollatzResearch.WordTrace tailWord_6218557 prefixEnd_6218557 3193108718381331600838883 := by
  unfold tailWord_6218557
  simp only [CollatzResearch.WordTrace]
  refine ⟨226809406932237508826989925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151206271288158339217993283 226809406932237508826989925)
  ·
    refine ⟨42526763799794532905060611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226809406932237508826989925 42526763799794532905060611)
    ·
      refine ⟨63790145699691799357590917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42526763799794532905060611 63790145699691799357590917)
      ·
        refine ⟨11960652318692212379548297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63790145699691799357590917 11960652318692212379548297)
        ·
          refine ⟨8970489239019159284661223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11960652318692212379548297 8970489239019159284661223)
          ·
            refine ⟨13455733858528738926991835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970489239019159284661223 13455733858528738926991835)
            ·
              refine ⟨20183600787793108390487753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13455733858528738926991835 20183600787793108390487753)
              ·
                refine ⟨15137700590844831292865815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20183600787793108390487753 15137700590844831292865815)
                ·
                  refine ⟨22706550886267246939298723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137700590844831292865815 22706550886267246939298723)
                  ·
                    refine ⟨34059826329400870408948085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22706550886267246939298723 34059826329400870408948085)
                    ·
                      refine ⟨3193108718381331600838883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34059826329400870408948085 3193108718381331600838883)
                      ·
                        rfl

theorem cell23_6218557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6218557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218557 prefixEnd_6218557 := by exact prefixLift 6218557
  have htrace : WordTrace (prefixWord ++ tailWord_6218557) baseStart_6218557 baseEnd_6218557 := by
    simpa [prefixWord, tailWord_6218557, baseEnd_6218557] using wordTrace_append hprefix tailTrace_6218557
  have hstable : (prefixWord ++ tailWord_6218557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218557).length < 2 ^ (prefixWord ++ tailWord_6218557).sum := by decide
  have hdescent : baseEnd_6218557 < baseStart_6218557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218570 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_6218570 : Nat := 118140960795 + 6218570 * 2 ^ 59
def prefixEnd_6218570 : Nat := 4983230072969 + 3 ^ 40 * 6218570 * 2
def baseEnd_6218570 : Nat := 3193115393629840049976323

theorem tailTrace_6218570 : CollatzResearch.WordTrace tailWord_6218570 prefixEnd_6218570 3193115393629840049976323 := by
  unfold tailWord_6218570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56702470270297603011803291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151206587387460274698142109 56702470270297603011803291)
  ·
    refine ⟨85053705405446404517704937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56702470270297603011803291 85053705405446404517704937)
    ·
      refine ⟨63790279054084803388278703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85053705405446404517704937 63790279054084803388278703)
      ·
        refine ⟨95685418581127205082418055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63790279054084803388278703 95685418581127205082418055)
        ·
          refine ⟨143528127871690807623627083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95685418581127205082418055 143528127871690807623627083)
          ·
            refine ⟨215292191807536211435440625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143528127871690807623627083 215292191807536211435440625)
            ·
              refine ⟨161469143855652158576580469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215292191807536211435440625 161469143855652158576580469)
              ·
                refine ⟨15137732236467389866554419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161469143855652158576580469 15137732236467389866554419)
                ·
                  refine ⟨22706598354701084799831629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137732236467389866554419 22706598354701084799831629)
                  ·
                    refine ⟨8514974383012906799936861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22706598354701084799831629 8514974383012906799936861)
                    ·
                      refine ⟨3193115393629840049976323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8514974383012906799936861 3193115393629840049976323)
                      ·
                        rfl

theorem cell23_6218570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_6218570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218570 prefixEnd_6218570 := by exact prefixLift 6218570
  have htrace : WordTrace (prefixWord ++ tailWord_6218570) baseStart_6218570 baseEnd_6218570 := by
    simpa [prefixWord, tailWord_6218570, baseEnd_6218570] using wordTrace_append hprefix tailTrace_6218570
  have hstable : (prefixWord ++ tailWord_6218570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218570).length < 2 ^ (prefixWord ++ tailWord_6218570).sum := by decide
  have hdescent : baseEnd_6218570 < baseStart_6218570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218577 : List Nat := [1, 2, 2, 1, 6, 2, 2, 7]
def baseStart_6218577 : Nat := 118140960795 + 6218577 * 2 ^ 59
def prefixEnd_6218577 : Nat := 4983230072969 + 3 ^ 40 * 6218577 * 2
def baseEnd_6218577 : Nat := 118263666222015611947733

theorem tailTrace_6218577 : CollatzResearch.WordTrace tailWord_6218577 prefixEnd_6218577 118263666222015611947733 := by
  unfold tailWord_6218577
  simp only [CollatzResearch.WordTrace]
  refine ⟨226810136392165052242717985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151206757594776701495145323 226810136392165052242717985)
  ·
    refine ⟨170107602294123789182038489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226810136392165052242717985 170107602294123789182038489)
    ·
      refine ⟨127580701720592841886528867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170107602294123789182038489 127580701720592841886528867)
      ·
        refine ⟨191371052580889262829793301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127580701720592841886528867 191371052580889262829793301)
        ·
          refine ⟨8970518089729184195146561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191371052580889262829793301 8970518089729184195146561)
          ·
            refine ⟨6727888567296888146359921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8970518089729184195146561 6727888567296888146359921)
            ·
              refine ⟨5045916425472666109769941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727888567296888146359921 5045916425472666109769941)
              ·
                refine ⟨118263666222015611947733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5045916425472666109769941 118263666222015611947733)
                ·
                  rfl

theorem cell23_6218577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 7].length) (baseStart_6218577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218577 prefixEnd_6218577 := by exact prefixLift 6218577
  have htrace : WordTrace (prefixWord ++ tailWord_6218577) baseStart_6218577 baseEnd_6218577 := by
    simpa [prefixWord, tailWord_6218577, baseEnd_6218577] using wordTrace_append hprefix tailTrace_6218577
  have hstable : (prefixWord ++ tailWord_6218577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218577).length < 2 ^ (prefixWord ++ tailWord_6218577).sum := by decide
  have hdescent : baseEnd_6218577 < baseStart_6218577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218588 : List Nat := [2, 2, 4, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6218588 : Nat := 118140960795 + 6218588 * 2 ^ 59
def prefixEnd_6218588 : Nat := 4983230072969 + 3 ^ 40 * 6218588 * 2
def baseEnd_6218588 : Nat := 3193124636281620979551241

theorem tailTrace_6218588 : CollatzResearch.WordTrace tailWord_6218588 prefixEnd_6218588 3193124636281620979551241 := by
  unfold tailWord_6218588
  simp only [CollatzResearch.WordTrace]
  refine ⟨113405268797562600560684209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151207025063416800747578945 113405268797562600560684209)
  ·
    refine ⟨85053951598171950420513157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113405268797562600560684209 85053951598171950420513157)
    ·
      refine ⟨15947615924657240703846217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85053951598171950420513157 15947615924657240703846217)
      ·
        refine ⟨11960711943492930527884663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15947615924657240703846217 11960711943492930527884663)
        ·
          refine ⟨17941067915239395791826995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11960711943492930527884663 17941067915239395791826995)
          ·
            refine ⟨26911601872859093687740493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17941067915239395791826995 26911601872859093687740493)
            ·
              refine ⟨10091850702322160132902685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26911601872859093687740493 10091850702322160132902685)
              ·
                refine ⟨3784444013370810049838507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10091850702322160132902685 3784444013370810049838507)
                ·
                  refine ⟨5676666020056215074757761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784444013370810049838507 5676666020056215074757761)
                  ·
                    refine ⟨4257499515042161306068321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676666020056215074757761 4257499515042161306068321)
                    ·
                      refine ⟨3193124636281620979551241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257499515042161306068321 3193124636281620979551241)
                      ·
                        rfl

theorem cell23_6218588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6218588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218588 prefixEnd_6218588 := by exact prefixLift 6218588
  have htrace : WordTrace (prefixWord ++ tailWord_6218588) baseStart_6218588 baseEnd_6218588 := by
    simpa [prefixWord, tailWord_6218588, baseEnd_6218588] using wordTrace_append hprefix tailTrace_6218588
  have hstable : (prefixWord ++ tailWord_6218588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218588).length < 2 ^ (prefixWord ++ tailWord_6218588).sum := by decide
  have hdescent : baseEnd_6218588 < baseStart_6218588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218603 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 4, 6]
def baseStart_6218603 : Nat := 118140960795 + 6218603 * 2 ^ 59
def prefixEnd_6218603 : Nat := 4983230072969 + 3 ^ 40 * 6218603 * 2
def baseEnd_6218603 : Nat := 1064377446163812806954557

theorem tailTrace_6218603 : CollatzResearch.WordTrace tailWord_6218603 prefixEnd_6218603 1064377446163812806954557 := by
  unfold tailWord_6218603
  simp only [CollatzResearch.WordTrace]
  refine ⟨226811084690070858683164463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151207389793380572455442975 226811084690070858683164463)
  ·
    refine ⟨340216627035106288024746695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226811084690070858683164463 340216627035106288024746695)
    ·
      refine ⟨510324940552659432037120043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340216627035106288024746695 510324940552659432037120043)
      ·
        refine ⟨765487410828989148055680065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510324940552659432037120043 765487410828989148055680065)
        ·
          refine ⟨574115558121741861041760049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765487410828989148055680065 574115558121741861041760049)
          ·
            refine ⟨430586668591306395781320037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574115558121741861041760049 430586668591306395781320037)
            ·
              refine ⟨80735000360869949208997507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 430586668591306395781320037 80735000360869949208997507)
              ·
                refine ⟨121102500541304923813496261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80735000360869949208997507 121102500541304923813496261)
                ·
                  refine ⟨22706718851494673215030549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121102500541304923813496261 22706718851494673215030549)
                  ·
                    refine ⟨1064377446163812806954557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22706718851494673215030549 1064377446163812806954557)
                    ·
                      rfl

theorem cell23_6218603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_6218603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218603 prefixEnd_6218603 := by exact prefixLift 6218603
  have htrace : WordTrace (prefixWord ++ tailWord_6218603) baseStart_6218603 baseEnd_6218603 := by
    simpa [prefixWord, tailWord_6218603, baseEnd_6218603] using wordTrace_append hprefix tailTrace_6218603
  have hstable : (prefixWord ++ tailWord_6218603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218603).length < 2 ^ (prefixWord ++ tailWord_6218603).sum := by decide
  have hdescent : baseEnd_6218603 < baseStart_6218603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218627 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 1, 4, 2]
def baseStart_6218627 : Nat := 118140960795 + 6218627 * 2 ^ 59
def prefixEnd_6218627 : Nat := 4983230072969 + 3 ^ 40 * 6218627 * 2
def baseEnd_6218627 : Nat := 3193144662027146326963561

theorem tailTrace_6218627 : CollatzResearch.WordTrace tailWord_6218627 prefixEnd_6218627 3193144662027146326963561 := by
  unfold tailWord_6218627
  simp only [CollatzResearch.WordTrace]
  refine ⟨226811960041983910782038135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151207973361322607188025423 226811960041983910782038135)
  ·
    refine ⟨340217940062975866173057203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226811960041983910782038135 340217940062975866173057203)
    ·
      refine ⟨510326910094463799259585805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340217940062975866173057203 510326910094463799259585805)
      ·
        refine ⟨191372591285423924722344677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510326910094463799259585805 191372591285423924722344677)
        ·
          refine ⟨35882360866016985885439627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191372591285423924722344677 35882360866016985885439627)
          ·
            refine ⟨53823541299025478828159441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35882360866016985885439627 53823541299025478828159441)
            ·
              refine ⟨40367655974269109121119581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53823541299025478828159441 40367655974269109121119581)
              ·
                refine ⟨15137870990350915920419843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40367655974269109121119581 15137870990350915920419843)
                ·
                  refine ⟨22706806485526373880629765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137870990350915920419843 22706806485526373880629765)
                  ·
                    refine ⟨4257526216036195102618081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22706806485526373880629765 4257526216036195102618081)
                    ·
                      refine ⟨3193144662027146326963561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257526216036195102618081 3193144662027146326963561)
                      ·
                        rfl

theorem cell23_6218627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_6218627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218627 prefixEnd_6218627 := by exact prefixLift 6218627
  have htrace : WordTrace (prefixWord ++ tailWord_6218627) baseStart_6218627 baseEnd_6218627 := by
    simpa [prefixWord, tailWord_6218627, baseEnd_6218627] using wordTrace_append hprefix tailTrace_6218627
  have hstable : (prefixWord ++ tailWord_6218627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218627).length < 2 ^ (prefixWord ++ tailWord_6218627).sum := by decide
  have hdescent : baseEnd_6218627 < baseStart_6218627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218631 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_6218631 : Nat := 118140960795 + 6218631 * 2 ^ 59
def prefixEnd_6218631 : Nat := 4983230072969 + 3 ^ 40 * 6218631 * 2
def baseEnd_6218631 : Nat := 3193146715949764311313543

theorem tailTrace_6218631 : CollatzResearch.WordTrace tailWord_6218631 prefixEnd_6218631 3193146715949764311313543 := by
  unfold tailWord_6218631
  simp only [CollatzResearch.WordTrace]
  refine ⟨226812105933969419465183747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151208070622646279643455831 226812105933969419465183747)
  ·
    refine ⟨340218158900954129197775621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226812105933969419465183747 340218158900954129197775621)
    ·
      refine ⟨63790904793928899224582929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340218158900954129197775621 63790904793928899224582929)
      ·
        refine ⟨47843178595446674418437197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63790904793928899224582929 47843178595446674418437197)
        ·
          refine ⟨17941191973292502906913949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47843178595446674418437197 17941191973292502906913949)
          ·
            refine ⟨6727946989984688590092731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17941191973292502906913949 6727946989984688590092731)
            ·
              refine ⟨10091920484977032885139097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727946989984688590092731 10091920484977032885139097)
              ·
                refine ⟨7568940363732774663854323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10091920484977032885139097 7568940363732774663854323)
                ·
                  refine ⟨11353410545599161995781485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7568940363732774663854323 11353410545599161995781485)
                  ·
                    refine ⟨4257528954599685748418057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11353410545599161995781485 4257528954599685748418057)
                    ·
                      refine ⟨3193146715949764311313543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257528954599685748418057 3193146715949764311313543)
                      ·
                        rfl

theorem cell23_6218631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_6218631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218631 prefixEnd_6218631 := by exact prefixLift 6218631
  have htrace : WordTrace (prefixWord ++ tailWord_6218631) baseStart_6218631 baseEnd_6218631 := by
    simpa [prefixWord, tailWord_6218631, baseEnd_6218631] using wordTrace_append hprefix tailTrace_6218631
  have hstable : (prefixWord ++ tailWord_6218631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218631).length < 2 ^ (prefixWord ++ tailWord_6218631).sum := by decide
  have hdescent : baseEnd_6218631 < baseStart_6218631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218643 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_6218643 : Nat := 118140960795 + 6218643 * 2 ^ 59
def prefixEnd_6218643 : Nat := 4983230072969 + 3 ^ 40 * 6218643 * 2
def baseEnd_6218643 : Nat := 3193152877717618264363487

theorem tailTrace_6218643 : CollatzResearch.WordTrace tailWord_6218643 prefixEnd_6218643 3193152877717618264363487 := by
  unfold tailWord_6218643
  simp only [CollatzResearch.WordTrace]
  refine ⟨226812543609925945514620583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151208362406617297009747055 226812543609925945514620583)
  ·
    refine ⟨340218815414888918271930875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226812543609925945514620583 340218815414888918271930875)
    ·
      refine ⟨510328223122333377407896313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340218815414888918271930875 510328223122333377407896313)
      ·
        refine ⟨382746167341750033055922235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510328223122333377407896313 382746167341750033055922235)
        ·
          refine ⟨574119251012625049583883353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382746167341750033055922235 574119251012625049583883353)
          ·
            refine ⟨430589438259468787187912515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574119251012625049583883353 430589438259468787187912515)
            ·
              refine ⟨645884157389203180781868773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430589438259468787187912515 645884157389203180781868773)
              ·
                refine ⟨121103279510475596396600395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645884157389203180781868773 121103279510475596396600395)
                ·
                  refine ⟨181654919265713394594900593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121103279510475596396600395 181654919265713394594900593)
                  ·
                    refine ⟨136241189449285045946175445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181654919265713394594900593 136241189449285045946175445)
                    ·
                      refine ⟨3193152877717618264363487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136241189449285045946175445 3193152877717618264363487)
                      ·
                        rfl

theorem cell23_6218643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_6218643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218643 prefixEnd_6218643 := by exact prefixLift 6218643
  have htrace : WordTrace (prefixWord ++ tailWord_6218643) baseStart_6218643 baseEnd_6218643 := by
    simpa [prefixWord, tailWord_6218643, baseEnd_6218643] using wordTrace_append hprefix tailTrace_6218643
  have hstable : (prefixWord ++ tailWord_6218643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218643).length < 2 ^ (prefixWord ++ tailWord_6218643).sum := by decide
  have hdescent : baseEnd_6218643 < baseStart_6218643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218644 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6218644 : Nat := 118140960795 + 6218644 * 2 ^ 59
def prefixEnd_6218644 : Nat := 4983230072969 + 3 ^ 40 * 6218644 * 2
def baseEnd_6218644 : Nat := 3193153391198272760450983

theorem tailTrace_6218644 : CollatzResearch.WordTrace tailWord_6218644 prefixEnd_6218644 3193153391198272760450983 := by
  unfold tailWord_6218644
  simp only [CollatzResearch.WordTrace]
  refine ⟨113406290041461161342703493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151208386721948215123604657 113406290041461161342703493)
  ·
    refine ⟨21263679382773967751756905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113406290041461161342703493 21263679382773967751756905)
    ·
      refine ⟨15947759537080475813817679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21263679382773967751756905 15947759537080475813817679)
      ·
        refine ⟨23921639305620713720726519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15947759537080475813817679 23921639305620713720726519)
        ·
          refine ⟨35882458958431070581089779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23921639305620713720726519 35882458958431070581089779)
          ·
            refine ⟨53823688437646605871634669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35882458958431070581089779 53823688437646605871634669)
            ·
              refine ⟨20183883164117477201863001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53823688437646605871634669 20183883164117477201863001)
              ·
                refine ⟨15137912373088107901397251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20183883164117477201863001 15137912373088107901397251)
                ·
                  refine ⟨22706868559632161852095877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15137912373088107901397251 22706868559632161852095877)
                  ·
                    refine ⟨4257537854931030347267977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22706868559632161852095877 4257537854931030347267977)
                    ·
                      refine ⟨3193153391198272760450983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257537854931030347267977 3193153391198272760450983)
                      ·
                        rfl

theorem cell23_6218644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6218644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218644 prefixEnd_6218644 := by exact prefixLift 6218644
  have htrace : WordTrace (prefixWord ++ tailWord_6218644) baseStart_6218644 baseEnd_6218644 := by
    simpa [prefixWord, tailWord_6218644, baseEnd_6218644] using wordTrace_append hprefix tailTrace_6218644
  have hstable : (prefixWord ++ tailWord_6218644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218644).length < 2 ^ (prefixWord ++ tailWord_6218644).sum := by decide
  have hdescent : baseEnd_6218644 < baseStart_6218644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218677 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_6218677 : Nat := 118140960795 + 6218677 * 2 ^ 59
def prefixEnd_6218677 : Nat := 4983230072969 + 3 ^ 40 * 6218677 * 2
def baseEnd_6218677 : Nat := 3193170336059871131338331

theorem tailTrace_6218677 : CollatzResearch.WordTrace tailWord_6218677 prefixEnd_6218677 3193170336059871131338331 := by
  unfold tailWord_6218677
  simp only [CollatzResearch.WordTrace]
  refine ⟨226813783691802769321358285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151209189127868512880905523 226813783691802769321358285)
  ·
    refine ⟨85055168884426038495509357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226813783691802769321358285 85055168884426038495509357)
    ·
      refine ⟨31895688331659764435816009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85055168884426038495509357 31895688331659764435816009)
      ·
        refine ⟨23921766248744823326862007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31895688331659764435816009 23921766248744823326862007)
        ·
          refine ⟨35882649373117234990293011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23921766248744823326862007 35882649373117234990293011)
          ·
            refine ⟨53823974059675852485439517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35882649373117234990293011 53823974059675852485439517)
            ·
              refine ⟨20183990272378444682039819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53823974059675852485439517 20183990272378444682039819)
              ·
                refine ⟨30275985408567667023059729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20183990272378444682039819 30275985408567667023059729)
                ·
                  refine ⟨22706989056425750267294797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30275985408567667023059729 22706989056425750267294797)
                  ·
                    refine ⟨8515120896159656350235549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22706989056425750267294797 8515120896159656350235549)
                    ·
                      refine ⟨3193170336059871131338331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515120896159656350235549 3193170336059871131338331)
                      ·
                        rfl

theorem cell23_6218677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_6218677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218677 prefixEnd_6218677 := by exact prefixLift 6218677
  have htrace : WordTrace (prefixWord ++ tailWord_6218677) baseStart_6218677 baseEnd_6218677 := by
    simpa [prefixWord, tailWord_6218677, baseEnd_6218677] using wordTrace_append hprefix tailTrace_6218677
  have hstable : (prefixWord ++ tailWord_6218677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218677).length < 2 ^ (prefixWord ++ tailWord_6218677).sum := by decide
  have hdescent : baseEnd_6218677 < baseStart_6218677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218737 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 3]
def baseStart_6218737 : Nat := 118140960795 + 6218737 * 2 ^ 59
def prefixEnd_6218737 : Nat := 4983230072969 + 3 ^ 40 * 6218737 * 2
def baseEnd_6218737 : Nat := 3193201144899140896588055

theorem tailTrace_6218737 : CollatzResearch.WordTrace tailWord_6218737 prefixEnd_6218737 3193201144899140896588055 := by
  unfold tailWord_6218737
  simp only [CollatzResearch.WordTrace]
  refine ⟨226815972071585399568542465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151210648047723599712361643 226815972071585399568542465)
  ·
    refine ⟨170111979053689049676406849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226815972071585399568542465 170111979053689049676406849)
    ·
      refine ⟨127583984290266787257305137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170111979053689049676406849 127583984290266787257305137)
      ·
        refine ⟨95687988217700090442978853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127583984290266787257305137 95687988217700090442978853)
        ·
          refine ⟨17941497790818766958058535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95687988217700090442978853 17941497790818766958058535)
          ·
            refine ⟨26912246686228150437087803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17941497790818766958058535 26912246686228150437087803)
            ·
              refine ⟨40368370029342225655631705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26912246686228150437087803 40368370029342225655631705)
              ·
                refine ⟨30276277522006669241723779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40368370029342225655631705 30276277522006669241723779)
                ·
                  refine ⟨45414416283010003862585669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30276277522006669241723779 45414416283010003862585669)
                  ·
                    refine ⟨8515203053064375724234813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45414416283010003862585669 8515203053064375724234813)
                    ·
                      refine ⟨3193201144899140896588055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515203053064375724234813 3193201144899140896588055)
                      ·
                        rfl

theorem cell23_6218737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_6218737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218737 prefixEnd_6218737 := by exact prefixLift 6218737
  have htrace : WordTrace (prefixWord ++ tailWord_6218737) baseStart_6218737 baseEnd_6218737 := by
    simpa [prefixWord, tailWord_6218737, baseEnd_6218737] using wordTrace_append hprefix tailTrace_6218737
  have hstable : (prefixWord ++ tailWord_6218737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218737).length < 2 ^ (prefixWord ++ tailWord_6218737).sum := by decide
  have hdescent : baseEnd_6218737 < baseStart_6218737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218791 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 6]
def baseStart_6218791 : Nat := 118140960795 + 6218791 * 2 ^ 59
def prefixEnd_6218791 : Nat := 4983230072969 + 3 ^ 40 * 6218791 * 2
def baseEnd_6218791 : Nat := 354803208094942631701423

theorem tailTrace_6218791 : CollatzResearch.WordTrace tailWord_6218791 prefixEnd_6218791 354803208094942631701423 := by
  unfold tailWord_6218791
  simp only [CollatzResearch.WordTrace]
  refine ⟨226817941613389766791008227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151211961075593177860672151 226817941613389766791008227)
  ·
    refine ⟨340226912420084650186512341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226817941613389766791008227 340226912420084650186512341)
    ·
      refine ⟨7974068259845733988746383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 340226912420084650186512341 7974068259845733988746383)
      ·
        refine ⟨11961102389768600983119575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7974068259845733988746383 11961102389768600983119575)
        ·
          refine ⟨17941653584652901474679363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961102389768600983119575 17941653584652901474679363)
          ·
            refine ⟨26912480376979352212019045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17941653584652901474679363 26912480376979352212019045)
            ·
              refine ⟨5046090070683628539753571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26912480376979352212019045 5046090070683628539753571)
              ·
                refine ⟨7569135106025442809630357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046090070683628539753571 7569135106025442809630357)
                ·
                  refine ⟨354803208094942631701423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7569135106025442809630357 354803208094942631701423)
                  ·
                    rfl

theorem cell23_6218791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 6].length) (baseStart_6218791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218791 prefixEnd_6218791 := by exact prefixLift 6218791
  have htrace : WordTrace (prefixWord ++ tailWord_6218791) baseStart_6218791 baseEnd_6218791 := by
    simpa [prefixWord, tailWord_6218791, baseEnd_6218791] using wordTrace_append hprefix tailTrace_6218791
  have hstable : (prefixWord ++ tailWord_6218791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218791).length < 2 ^ (prefixWord ++ tailWord_6218791).sum := by decide
  have hdescent : baseEnd_6218791 < baseStart_6218791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218827 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3]
def baseStart_6218827 : Nat := 118140960795 + 6218827 * 2 ^ 59
def prefixEnd_6218827 : Nat := 4983230072969 + 3 ^ 40 * 6218827 * 2
def baseEnd_6218827 : Nat := 3193247358158045544462641

theorem tailTrace_6218827 : CollatzResearch.WordTrace tailWord_6218827 prefixEnd_6218827 3193247358158045544462641 := by
  unfold tailWord_6218827
  simp only [CollatzResearch.WordTrace]
  refine ⟨226819254641259344939318735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151212836427506229959545823 226819254641259344939318735)
  ·
    refine ⟨340228881961889017408978103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226819254641259344939318735 340228881961889017408978103)
    ·
      refine ⟨510343322942833526113467155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340228881961889017408978103 510343322942833526113467155)
      ·
        refine ⟨765514984414250289170200733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510343322942833526113467155 765514984414250289170200733)
        ·
          refine ⟨287068119155343858438825275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765514984414250289170200733 287068119155343858438825275)
          ·
            refine ⟨430602178733015787658237913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287068119155343858438825275 430602178733015787658237913)
            ·
              refine ⟨322951634049761840743678435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430602178733015787658237913 322951634049761840743678435)
              ·
                refine ⟨484427451074642761115517653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322951634049761840743678435 484427451074642761115517653)
                ·
                  refine ⟨11353768384561939713644945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 484427451074642761115517653 11353768384561939713644945)
                  ·
                    refine ⟨8515326288421454785233709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11353768384561939713644945 8515326288421454785233709)
                    ·
                      refine ⟨3193247358158045544462641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515326288421454785233709 3193247358158045544462641)
                      ·
                        rfl

theorem cell23_6218827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 3].length) (baseStart_6218827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218827 prefixEnd_6218827 := by exact prefixLift 6218827
  have htrace : WordTrace (prefixWord ++ tailWord_6218827) baseStart_6218827 baseEnd_6218827 := by
    simpa [prefixWord, tailWord_6218827, baseEnd_6218827] using wordTrace_append hprefix tailTrace_6218827
  have hstable : (prefixWord ++ tailWord_6218827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218827).length < 2 ^ (prefixWord ++ tailWord_6218827).sum := by decide
  have hdescent : baseEnd_6218827 < baseStart_6218827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218837 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6218837 : Nat := 118140960795 + 6218837 * 2 ^ 59
def prefixEnd_6218837 : Nat := 4983230072969 + 3 ^ 40 * 6218837 * 2
def baseEnd_6218837 : Nat := 3193252492964590505337595

theorem tailTrace_6218837 : CollatzResearch.WordTrace tailWord_6218837 prefixEnd_6218837 3193252492964590505337595 := by
  unfold tailWord_6218837
  simp only [CollatzResearch.WordTrace]
  refine ⟨226819619371223116647182765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151213079580815411098121843 226819619371223116647182765)
  ·
    refine ⟨85057357264208668742693537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226819619371223116647182765 85057357264208668742693537)
    ·
      refine ⟨63793017948156501557020153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85057357264208668742693537 63793017948156501557020153)
      ·
        refine ⟨47844763461117376167765115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63793017948156501557020153 47844763461117376167765115)
        ·
          refine ⟨71767145191676064251647673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47844763461117376167765115 71767145191676064251647673)
          ·
            refine ⟨53825358893757048188735755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71767145191676064251647673 53825358893757048188735755)
            ·
              refine ⟨80738038340635572283103633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53825358893757048188735755 80738038340635572283103633)
              ·
                refine ⟨60553528755476679212327725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80738038340635572283103633 60553528755476679212327725)
                ·
                  refine ⟨22707573283303754704622897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60553528755476679212327725 22707573283303754704622897)
                  ·
                    refine ⟨17030679962477816028467173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22707573283303754704622897 17030679962477816028467173)
                    ·
                      refine ⟨3193252492964590505337595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17030679962477816028467173 3193252492964590505337595)
                      ·
                        rfl

theorem cell23_6218837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6218837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218837 prefixEnd_6218837 := by exact prefixLift 6218837
  have htrace : WordTrace (prefixWord ++ tailWord_6218837) baseStart_6218837 baseEnd_6218837 := by
    simpa [prefixWord, tailWord_6218837, baseEnd_6218837] using wordTrace_append hprefix tailTrace_6218837
  have hstable : (prefixWord ++ tailWord_6218837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218837).length < 2 ^ (prefixWord ++ tailWord_6218837).sum := by decide
  have hdescent : baseEnd_6218837 < baseStart_6218837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218844 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_6218844 : Nat := 118140960795 + 6218844 * 2 ^ 59
def prefixEnd_6218844 : Nat := 4983230072969 + 3 ^ 40 * 6218844 * 2
def baseEnd_6218844 : Nat := 3193256087329171977950063

theorem tailTrace_6218844 : CollatzResearch.WordTrace tailWord_6218844 prefixEnd_6218844 3193256087329171977950063 := by
  unfold tailWord_6218844
  simp only [CollatzResearch.WordTrace]
  refine ⟨113409937341098878421343793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151213249788131837895125057 113409937341098878421343793)
  ·
    refine ⟨85057453005824158816007845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113409937341098878421343793 85057453005824158816007845)
    ·
      refine ⟨15948272438592029778001471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85057453005824158816007845 15948272438592029778001471)
      ·
        refine ⟨23922408657888044667002207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15948272438592029778001471 23922408657888044667002207)
        ·
          refine ⟨35883612986832067000503311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23922408657888044667002207 35883612986832067000503311)
          ·
            refine ⟨53825419480248100500754967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35883612986832067000503311 53825419480248100500754967)
            ·
              refine ⟨80738129220372150751132451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53825419480248100500754967 80738129220372150751132451)
              ·
                refine ⟨121107193830558226126698677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80738129220372150751132451 121107193830558226126698677)
                ·
                  refine ⟨11353799421614833699378001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121107193830558226126698677 11353799421614833699378001)
                  ·
                    refine ⟨8515349566211125274533501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11353799421614833699378001 8515349566211125274533501)
                    ·
                      refine ⟨3193256087329171977950063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515349566211125274533501 3193256087329171977950063)
                      ·
                        rfl

theorem cell23_6218844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_6218844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218844 prefixEnd_6218844 := by exact prefixLift 6218844
  have htrace : WordTrace (prefixWord ++ tailWord_6218844) baseStart_6218844 baseEnd_6218844 := by
    simpa [prefixWord, tailWord_6218844, baseEnd_6218844] using wordTrace_append hprefix tailTrace_6218844
  have hstable : (prefixWord ++ tailWord_6218844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218844).length < 2 ^ (prefixWord ++ tailWord_6218844).sum := by decide
  have hdescent : baseEnd_6218844 < baseStart_6218844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218858 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6218858 : Nat := 118140960795 + 6218858 * 2 ^ 59
def prefixEnd_6218858 : Nat := 4983230072969 + 3 ^ 40 * 6218858 * 2
def baseEnd_6218858 : Nat := 3193263276058334923174999

theorem tailTrace_6218858 : CollatzResearch.WordTrace tailWord_6218858 prefixEnd_6218858 3193263276058334923174999 := by
  unfold tailWord_6218858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56705096326036759308424307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151213590202764691489131485 56705096326036759308424307)
  ·
    refine ⟨85057644489055138962636461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56705096326036759308424307 85057644489055138962636461)
    ·
      refine ⟨31896616683395677110988673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85057644489055138962636461 31896616683395677110988673)
      ·
        refine ⟨23922462512546757833241505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31896616683395677110988673 23922462512546757833241505)
        ·
          refine ⟨17941846884410068374931129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23922462512546757833241505 17941846884410068374931129)
          ·
            refine ⟨13456385163307551281198347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17941846884410068374931129 13456385163307551281198347)
            ·
              refine ⟨20184577744961326921797521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13456385163307551281198347 20184577744961326921797521)
              ·
                refine ⟨15138433308720995191348141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20184577744961326921797521 15138433308720995191348141)
                ·
                  refine ⟨5676912490770373196755553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15138433308720995191348141 5676912490770373196755553)
                  ·
                    refine ⟨4257684368077779897566665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676912490770373196755553 4257684368077779897566665)
                    ·
                      refine ⟨3193263276058334923174999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257684368077779897566665 3193263276058334923174999)
                      ·
                        rfl

theorem cell23_6218858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6218858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218858 prefixEnd_6218858 := by exact prefixLift 6218858
  have htrace : WordTrace (prefixWord ++ tailWord_6218858) baseStart_6218858 baseEnd_6218858 := by
    simpa [prefixWord, tailWord_6218858, baseEnd_6218858] using wordTrace_append hprefix tailTrace_6218858
  have hstable : (prefixWord ++ tailWord_6218858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218858).length < 2 ^ (prefixWord ++ tailWord_6218858).sum := by decide
  have hdescent : baseEnd_6218858 < baseStart_6218858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218927 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_6218927 : Nat := 118140960795 + 6218927 * 2 ^ 59
def prefixEnd_6218927 : Nat := 4983230072969 + 3 ^ 40 * 6218927 * 2
def baseEnd_6218927 : Nat := 3193298706223495153212181

theorem tailTrace_6218927 : CollatzResearch.WordTrace tailWord_6218927 prefixEnd_6218927 3193298706223495153212181 := by
  unfold tailWord_6218927
  simp only [CollatzResearch.WordTrace]
  refine ⟨226822901940897062017959035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151215267960598041345306023 226822901940897062017959035)
  ·
    refine ⟨340234352911345593026938553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226822901940897062017959035 340234352911345593026938553)
    ·
      refine ⟨255175764683509194770203915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340234352911345593026938553 255175764683509194770203915)
      ·
        refine ⟨382763647025263792155305873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255175764683509194770203915 382763647025263792155305873)
        ·
          refine ⟨287072735268947844116479405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382763647025263792155305873 287072735268947844116479405)
          ·
            refine ⟨107652275725855441543679777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287072735268947844116479405 107652275725855441543679777)
            ·
              refine ⟨80739206794391581157759833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107652275725855441543679777 80739206794391581157759833)
              ·
                refine ⟨60554405095793685868319875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80739206794391581157759833 60554405095793685868319875)
                ·
                  refine ⟨90831607643690528802479813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60554405095793685868319875 90831607643690528802479813)
                  ·
                    refine ⟨17030926433191974150464965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90831607643690528802479813 17030926433191974150464965)
                    ·
                      refine ⟨3193298706223495153212181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17030926433191974150464965 3193298706223495153212181)
                      ·
                        rfl

theorem cell23_6218927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_6218927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218927 prefixEnd_6218927 := by exact prefixLift 6218927
  have htrace : WordTrace (prefixWord ++ tailWord_6218927) baseStart_6218927 baseEnd_6218927 := by
    simpa [prefixWord, tailWord_6218927, baseEnd_6218927] using wordTrace_append hprefix tailTrace_6218927
  have hstable : (prefixWord ++ tailWord_6218927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218927).length < 2 ^ (prefixWord ++ tailWord_6218927).sum := by decide
  have hdescent : baseEnd_6218927 < baseStart_6218927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218931 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 4, 2, 2]
def baseStart_6218931 : Nat := 118140960795 + 6218931 * 2 ^ 59
def prefixEnd_6218931 : Nat := 4983230072969 + 3 ^ 40 * 6218931 * 2
def baseEnd_6218931 : Nat := 3193300760146113137562163

theorem tailTrace_6218931 : CollatzResearch.WordTrace tailWord_6218931 prefixEnd_6218931 3193300760146113137562163 := by
  unfold tailWord_6218931
  simp only [CollatzResearch.WordTrace]
  refine ⟨226823047832882570701104647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151215365221921713800736431 226823047832882570701104647)
  ·
    refine ⟨340234571749323856051656971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226823047832882570701104647 340234571749323856051656971)
    ·
      refine ⟨510351857623985784077485457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340234571749323856051656971 510351857623985784077485457)
      ·
        refine ⟨382763893217989338058114093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510351857623985784077485457 382763893217989338058114093)
        ·
          refine ⟨143536459956746001771792785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382763893217989338058114093 143536459956746001771792785)
          ·
            refine ⟨107652344967559501328844589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143536459956746001771792785 107652344967559501328844589)
            ·
              refine ⟨40369629362834812998316721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107652344967559501328844589 40369629362834812998316721)
              ·
                refine ⟨30277222022126109748737541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40369629362834812998316721 30277222022126109748737541)
                ·
                  refine ⟨5676979129148645577888289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30277222022126109748737541 5676979129148645577888289)
                  ·
                    refine ⟨4257734346861484183416217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5676979129148645577888289 4257734346861484183416217)
                    ·
                      refine ⟨3193300760146113137562163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257734346861484183416217 3193300760146113137562163)
                      ·
                        rfl

theorem cell23_6218931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2, 2].length) (baseStart_6218931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218931 prefixEnd_6218931 := by exact prefixLift 6218931
  have htrace : WordTrace (prefixWord ++ tailWord_6218931) baseStart_6218931 baseEnd_6218931 := by
    simpa [prefixWord, tailWord_6218931, baseEnd_6218931] using wordTrace_append hprefix tailTrace_6218931
  have hstable : (prefixWord ++ tailWord_6218931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218931).length < 2 ^ (prefixWord ++ tailWord_6218931).sum := by decide
  have hdescent : baseEnd_6218931 < baseStart_6218931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218954 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_6218954 : Nat := 118140960795 + 6218954 * 2 ^ 59
def prefixEnd_6218954 : Nat := 4983230072969 + 3 ^ 40 * 6218954 * 2
def baseEnd_6218954 : Nat := 354812507800129616397173

theorem tailTrace_6218954 : CollatzResearch.WordTrace tailWord_6218954 prefixEnd_6218954 354812507800129616397173 := by
  unfold tailWord_6218954
  simp only [CollatzResearch.WordTrace]
  refine ⟨56705971677949811407297979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151215924474532830419461277 56705971677949811407297979)
  ·
    refine ⟨85058957516924717110946969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56705971677949811407297979 85058957516924717110946969)
    ·
      refine ⟨63794218137693537833210227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85058957516924717110946969 63794218137693537833210227)
      ·
        refine ⟨95691327206540306749815341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63794218137693537833210227 95691327206540306749815341)
        ·
          refine ⟨35884247702452615031180753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95691327206540306749815341 35884247702452615031180753)
          ·
            refine ⟨26913185776839461273385565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35884247702452615031180753 26913185776839461273385565)
            ·
              refine ⟨10092444666314797977519587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26913185776839461273385565 10092444666314797977519587)
              ·
                refine ⟨15138666999472196966279381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10092444666314797977519587 15138666999472196966279381)
                ·
                  refine ⟨354812507800129616397173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15138666999472196966279381 354812507800129616397173)
                  ·
                    rfl

theorem cell23_6218954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_6218954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218954 prefixEnd_6218954 := by exact prefixLift 6218954
  have htrace : WordTrace (prefixWord ++ tailWord_6218954) baseStart_6218954 baseEnd_6218954 := by
    simpa [prefixWord, tailWord_6218954, baseEnd_6218954] using wordTrace_append hprefix tailTrace_6218954
  have hstable : (prefixWord ++ tailWord_6218954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218954).length < 2 ^ (prefixWord ++ tailWord_6218954).sum := by decide
  have hdescent : baseEnd_6218954 < baseStart_6218954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218965 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6218965 : Nat := 118140960795 + 6218965 * 2 ^ 59
def prefixEnd_6218965 : Nat := 4983230072969 + 3 ^ 40 * 6218965 * 2
def baseEnd_6218965 : Nat := 3193318218488366004537007

theorem tailTrace_6218965 : CollatzResearch.WordTrace tailWord_6218965 prefixEnd_6218965 3193318218488366004537007 := by
  unfold tailWord_6218965
  simp only [CollatzResearch.WordTrace]
  refine ⟨226824287914759394507842349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151216191943172929671894899 226824287914759394507842349)
  ·
    refine ⟨85059107968034772940440881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226824287914759394507842349 85059107968034772940440881)
    ·
      refine ⟨63794330976026079705330661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85059107968034772940440881 63794330976026079705330661)
      ·
        refine ⟨11961437058004889944749499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63794330976026079705330661 11961437058004889944749499)
        ·
          refine ⟨17942155587007334917124249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11961437058004889944749499 17942155587007334917124249)
          ·
            refine ⟨13456616690255501187843187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17942155587007334917124249 13456616690255501187843187)
            ·
              refine ⟨20184925035383251781764781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13456616690255501187843187 20184925035383251781764781)
              ·
                refine ⟨7569346888268719418161793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20184925035383251781764781 7569346888268719418161793)
                ·
                  refine ⟨5677010166201539563621345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7569346888268719418161793 5677010166201539563621345)
                  ·
                    refine ⟨4257757624651154672716009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5677010166201539563621345 4257757624651154672716009)
                    ·
                      refine ⟨3193318218488366004537007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257757624651154672716009 3193318218488366004537007)
                      ·
                        rfl

theorem cell23_6218965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6218965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218965 prefixEnd_6218965 := by exact prefixLift 6218965
  have htrace : WordTrace (prefixWord ++ tailWord_6218965) baseStart_6218965 baseEnd_6218965 := by
    simpa [prefixWord, tailWord_6218965, baseEnd_6218965] using wordTrace_append hprefix tailTrace_6218965
  have hstable : (prefixWord ++ tailWord_6218965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218965).length < 2 ^ (prefixWord ++ tailWord_6218965).sum := by decide
  have hdescent : baseEnd_6218965 < baseStart_6218965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6218967 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 7]
def baseStart_6218967 : Nat := 118140960795 + 6218967 * 2 ^ 59
def prefixEnd_6218967 : Nat := 4983230072969 + 3 ^ 40 * 6218967 * 2
def baseEnd_6218967 : Nat := 1064439748483224998903999

theorem tailTrace_6218967 : CollatzResearch.WordTrace tailWord_6218967 prefixEnd_6218967 1064439748483224998903999 := by
  unfold tailWord_6218967
  simp only [CollatzResearch.WordTrace]
  refine ⟨226824360860752148849415155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151216240573834765899610103 226824360860752148849415155)
  ·
    refine ⟨340236541291128223274122733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226824360860752148849415155 340236541291128223274122733)
    ·
      refine ⟨127588702984173083727796025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340236541291128223274122733 127588702984173083727796025)
      ·
        refine ⟨95691527238129812795847019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127588702984173083727796025 95691527238129812795847019)
        ·
          refine ⟨143537290857194719193770529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95691527238129812795847019 143537290857194719193770529)
          ·
            refine ⟨107652968142896039395327897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143537290857194719193770529 107652968142896039395327897)
            ·
              refine ⟨80739726107172029546495923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107652968142896039395327897 80739726107172029546495923)
              ·
                refine ⟨121109589160758044319743885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80739726107172029546495923 121109589160758044319743885)
                ·
                  refine ⟨45416095935284266619903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121109589160758044319743885 45416095935284266619903957)
                  ·
                    refine ⟨1064439748483224998903999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45416095935284266619903957 1064439748483224998903999)
                    ·
                      rfl

theorem cell23_6218967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_6218967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6218967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6218967 prefixEnd_6218967 := by exact prefixLift 6218967
  have htrace : WordTrace (prefixWord ++ tailWord_6218967) baseStart_6218967 baseEnd_6218967 := by
    simpa [prefixWord, tailWord_6218967, baseEnd_6218967] using wordTrace_append hprefix tailTrace_6218967
  have hstable : (prefixWord ++ tailWord_6218967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6218967).length < 2 ^ (prefixWord ++ tailWord_6218967).sum := by decide
  have hdescent : baseEnd_6218967 < baseStart_6218967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6218967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219027 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 12]
def baseStart_6219027 : Nat := 118140960795 + 6219027 * 2 ^ 59
def prefixEnd_6219027 : Nat := 4983230072969 + 3 ^ 40 * 6219027 * 2
def baseEnd_6219027 : Nat := 354816672698771640217969

theorem tailTrace_6219027 : CollatzResearch.WordTrace tailWord_6219027 prefixEnd_6219027 354816672698771640217969 := by
  unfold tailWord_6219027
  simp only [CollatzResearch.WordTrace]
  refine ⟨226826549240534779096599335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151217699493689852731066223 226826549240534779096599335)
  ·
    refine ⟨340239823860802168644899003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226826549240534779096599335 340239823860802168644899003)
    ·
      refine ⟨510359735791203252967348505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340239823860802168644899003 510359735791203252967348505)
      ·
        refine ⟨382769801843402439725511379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510359735791203252967348505 382769801843402439725511379)
        ·
          refine ⟨574154702765103659588267069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382769801843402439725511379 574154702765103659588267069)
          ·
            refine ⟨215308013536913872345600151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574154702765103659588267069 215308013536913872345600151)
            ·
              refine ⟨322962020305370808518400227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215308013536913872345600151 322962020305370808518400227)
              ·
                refine ⟨484443030458056212777600341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322962020305370808518400227 484443030458056212777600341)
                ·
                  refine ⟨354816672698771640217969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 484443030458056212777600341 354816672698771640217969)
                  ·
                    rfl

theorem cell23_6219027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 12].length) (baseStart_6219027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219027 prefixEnd_6219027 := by exact prefixLift 6219027
  have htrace : WordTrace (prefixWord ++ tailWord_6219027) baseStart_6219027 baseEnd_6219027 := by
    simpa [prefixWord, tailWord_6219027, baseEnd_6219027] using wordTrace_append hprefix tailTrace_6219027
  have hstable : (prefixWord ++ tailWord_6219027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219027).length < 2 ^ (prefixWord ++ tailWord_6219027).sum := by decide
  have hdescent : baseEnd_6219027 < baseStart_6219027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219031 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 3, 4]
def baseStart_6219031 : Nat := 118140960795 + 6219031 * 2 ^ 59
def prefixEnd_6219031 : Nat := 4983230072969 + 3 ^ 40 * 6219031 * 2
def baseEnd_6219031 : Nat := 1064450702737187582103901

theorem tailTrace_6219031 : CollatzResearch.WordTrace tailWord_6219031 prefixEnd_6219031 1064450702737187582103901 := by
  unfold tailWord_6219031
  simp only [CollatzResearch.WordTrace]
  refine ⟨226826695132520287779744947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151217796755013525186496631 226826695132520287779744947)
  ·
    refine ⟨340240042698780431669617421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226826695132520287779744947 340240042698780431669617421)
    ·
      refine ⟨127590016012042661876106533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340240042698780431669617421 127590016012042661876106533)
      ·
        refine ⟨23923128002257999101769975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127590016012042661876106533 23923128002257999101769975)
        ·
          refine ⟨35884692003386998652654963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23923128002257999101769975 35884692003386998652654963)
          ·
            refine ⟨53827038005080497978982445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35884692003386998652654963 53827038005080497978982445)
            ·
              refine ⟨20185139251905186742118417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53827038005080497978982445 20185139251905186742118417)
              ·
                refine ⟨15138854438928890056588813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20185139251905186742118417 15138854438928890056588813)
                ·
                  refine ⟨5677070414598333771220805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15138854438928890056588813 5677070414598333771220805)
                  ·
                    refine ⟨1064450702737187582103901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5677070414598333771220805 1064450702737187582103901)
                    ·
                      rfl

theorem cell23_6219031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_6219031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219031 prefixEnd_6219031 := by exact prefixLift 6219031
  have htrace : WordTrace (prefixWord ++ tailWord_6219031) baseStart_6219031 baseEnd_6219031 := by
    simpa [prefixWord, tailWord_6219031, baseEnd_6219031] using wordTrace_append hprefix tailTrace_6219031
  have hstable : (prefixWord ++ tailWord_6219031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219031).length < 2 ^ (prefixWord ++ tailWord_6219031).sum := by decide
  have hdescent : baseEnd_6219031 < baseStart_6219031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219044 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 8]
def baseStart_6219044 : Nat := 118140960795 + 6219044 * 2 ^ 59
def prefixEnd_6219044 : Nat := 4983230072969 + 3 ^ 40 * 6219044 * 2
def baseEnd_6219044 : Nat := 354817642606674577272127

theorem tailTrace_6219044 : CollatzResearch.WordTrace tailWord_6219044 prefixEnd_6219044 354817642606674577272127 := by
  unfold tailWord_6219044
  simp only [CollatzResearch.WordTrace]
  refine ⟨113413584640736595499984093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151218112854315460666645457 113413584640736595499984093)
  ·
    refine ⟨42530094240276223312494035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113413584640736595499984093 42530094240276223312494035)
    ·
      refine ⟨63795141360414334968741053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42530094240276223312494035 63795141360414334968741053)
      ·
        refine ⟨23923178010155375613277895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63795141360414334968741053 23923178010155375613277895)
        ·
          refine ⟨35884767015233063419916843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23923178010155375613277895 35884767015233063419916843)
          ·
            refine ⟨53827150522849595129875265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35884767015233063419916843 53827150522849595129875265)
            ·
              refine ⟨40370362892137196347406449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53827150522849595129875265 40370362892137196347406449)
              ·
                refine ⟨30277772169102897260554837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40370362892137196347406449 30277772169102897260554837)
                ·
                  refine ⟨354817642606674577272127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30277772169102897260554837 354817642606674577272127)
                  ·
                    rfl

theorem cell23_6219044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_6219044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219044 prefixEnd_6219044 := by exact prefixLift 6219044
  have htrace : WordTrace (prefixWord ++ tailWord_6219044) baseStart_6219044 baseEnd_6219044 := by
    simpa [prefixWord, tailWord_6219044, baseEnd_6219044] using wordTrace_append hprefix tailTrace_6219044
  have hstable : (prefixWord ++ tailWord_6219044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219044).length < 2 ^ (prefixWord ++ tailWord_6219044).sum := by decide
  have hdescent : baseEnd_6219044 < baseStart_6219044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219061 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 6]
def baseStart_6219061 : Nat := 118140960795 + 6219061 * 2 ^ 59
def prefixEnd_6219061 : Nat := 4983230072969 + 3 ^ 40 * 6219061 * 2
def baseEnd_6219061 : Nat := 354818612514577514326285

theorem tailTrace_6219061 : CollatzResearch.WordTrace tailWord_6219061 prefixEnd_6219061 354818612514577514326285 := by
  unfold tailWord_6219061
  simp only [CollatzResearch.WordTrace]
  refine ⟨226827789322411602903337037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151218526214941068602224691 226827789322411602903337037)
  ·
    refine ⟨85060420995904351088751389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226827789322411602903337037 85060420995904351088751389)
    ·
      refine ⟨31897657873464131658281771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85060420995904351088751389 31897657873464131658281771)
      ·
        refine ⟨47846486810196197487422657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31897657873464131658281771 47846486810196197487422657)
        ·
          refine ⟨35884865107647148115566993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47846486810196197487422657 35884865107647148115566993)
          ·
            refine ⟨26913648830735361086675245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35884865107647148115566993 26913648830735361086675245)
            ·
              refine ⟨10092618311525760407503217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26913648830735361086675245 10092618311525760407503217)
              ·
                refine ⟨7569463733644320305627413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10092618311525760407503217 7569463733644320305627413)
                ·
                  refine ⟨354818612514577514326285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7569463733644320305627413 354818612514577514326285)
                  ·
                    rfl

theorem cell23_6219061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_6219061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219061 prefixEnd_6219061 := by exact prefixLift 6219061
  have htrace : WordTrace (prefixWord ++ tailWord_6219061) baseStart_6219061 baseEnd_6219061 := by
    simpa [prefixWord, tailWord_6219061, baseEnd_6219061] using wordTrace_append hprefix tailTrace_6219061
  have hstable : (prefixWord ++ tailWord_6219061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219061).length < 2 ^ (prefixWord ++ tailWord_6219061).sum := by decide
  have hdescent : baseEnd_6219061 < baseStart_6219061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219081 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 5, 2]
def baseStart_6219081 : Nat := 118140960795 + 6219081 * 2 ^ 59
def prefixEnd_6219081 : Nat := 4983230072969 + 3 ^ 40 * 6219081 * 2
def baseEnd_6219081 : Nat := 3193377782244287550686473

theorem tailTrace_6219081 : CollatzResearch.WordTrace tailWord_6219081 prefixEnd_6219081 3193377782244287550686473 := by
  unfold tailWord_6219081
  simp only [CollatzResearch.WordTrace]
  refine ⟨226828518782339146319065097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151219012521559430879376731 226828518782339146319065097)
  ·
    refine ⟨170121389086754359739298823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226828518782339146319065097 170121389086754359739298823)
    ·
      refine ⟨255182083630131539608948235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170121389086754359739298823 255182083630131539608948235)
      ·
        refine ⟨382773125445197309413422353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255182083630131539608948235 382773125445197309413422353)
        ·
          refine ⟨287079844083897982060066765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382773125445197309413422353 287079844083897982060066765)
          ·
            refine ⟨107654941531461743272525037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287079844083897982060066765 107654941531461743272525037)
            ·
              refine ⟨40370603074298153727196889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107654941531461743272525037 40370603074298153727196889)
              ·
                refine ⟨30277952305723615295397667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40370603074298153727196889 30277952305723615295397667)
                ·
                  refine ⟨45416928458585422943096501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30277952305723615295397667 45416928458585422943096501)
                  ·
                    refine ⟨4257837042992383400915297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45416928458585422943096501 4257837042992383400915297)
                    ·
                      refine ⟨3193377782244287550686473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257837042992383400915297 3193377782244287550686473)
                      ·
                        rfl

theorem cell23_6219081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5, 2].length) (baseStart_6219081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219081 prefixEnd_6219081 := by exact prefixLift 6219081
  have htrace : WordTrace (prefixWord ++ tailWord_6219081) baseStart_6219081 baseEnd_6219081 := by
    simpa [prefixWord, tailWord_6219081, baseEnd_6219081] using wordTrace_append hprefix tailTrace_6219081
  have hstable : (prefixWord ++ tailWord_6219081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219081).length < 2 ^ (prefixWord ++ tailWord_6219081).sum := by decide
  have hdescent : baseEnd_6219081 < baseStart_6219081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219091 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 1, 5]
def baseStart_6219091 : Nat := 118140960795 + 6219091 * 2 ^ 59
def prefixEnd_6219091 : Nat := 4983230072969 + 3 ^ 40 * 6219091 * 2
def baseEnd_6219091 : Nat := 1064460972350277503853809

theorem tailTrace_6219091 : CollatzResearch.WordTrace tailWord_6219091 prefixEnd_6219091 1064460972350277503853809 := by
  unfold tailWord_6219091
  simp only [CollatzResearch.WordTrace]
  refine ⟨226828883512302918026929127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151219255674868612017952751 226828883512302918026929127)
  ·
    refine ⟨340243325268454377040393691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226828883512302918026929127 340243325268454377040393691)
    ·
      refine ⟨510364987902681565560590537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340243325268454377040393691 510364987902681565560590537)
      ·
        refine ⟨382773740927011174170442903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510364987902681565560590537 382773740927011174170442903)
        ·
          refine ⟨574160611390516761255664355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382773740927011174170442903 574160611390516761255664355)
          ·
            refine ⟨861240917085775141883496533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574160611390516761255664355 861240917085775141883496533)
            ·
              refine ⟨10092666997098927443947225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 861240917085775141883496533 10092666997098927443947225)
              ·
                refine ⟨7569500247824195582960419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10092666997098927443947225 7569500247824195582960419)
                ·
                  refine ⟨11354250371736293374440629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569500247824195582960419 11354250371736293374440629)
                  ·
                    refine ⟨1064460972350277503853809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11354250371736293374440629 1064460972350277503853809)
                    ·
                      rfl

theorem cell23_6219091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 5].length) (baseStart_6219091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219091 prefixEnd_6219091 := by exact prefixLift 6219091
  have htrace : WordTrace (prefixWord ++ tailWord_6219091) baseStart_6219091 baseEnd_6219091 := by
    simpa [prefixWord, tailWord_6219091, baseEnd_6219091] using wordTrace_append hprefix tailTrace_6219091
  have hstable : (prefixWord ++ tailWord_6219091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219091).length < 2 ^ (prefixWord ++ tailWord_6219091).sum := by decide
  have hdescent : baseEnd_6219091 < baseStart_6219091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219121 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_6219121 : Nat := 118140960795 + 6219121 * 2 ^ 59
def prefixEnd_6219121 : Nat := 4983230072969 + 3 ^ 40 * 6219121 * 2
def baseEnd_6219121 : Nat := 1064466107156822464728763

theorem tailTrace_6219121 : CollatzResearch.WordTrace tailWord_6219121 prefixEnd_6219121 1064466107156822464728763 := by
  unfold tailWord_6219121
  simp only [CollatzResearch.WordTrace]
  refine ⟨226829977702194233150521217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151219985134796155433680811 226829977702194233150521217)
  ·
    refine ⟨170122483276645674862890913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226829977702194233150521217 170122483276645674862890913)
    ·
      refine ⟨127591862457484256147168185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170122483276645674862890913 127591862457484256147168185)
      ·
        refine ⟨95693896843113192110376139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127591862457484256147168185 95693896843113192110376139)
        ·
          refine ⟨143540845264669788165564209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95693896843113192110376139 143540845264669788165564209)
          ·
            refine ⟨107655633948502341124173157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143540845264669788165564209 107655633948502341124173157)
            ·
              refine ⟨20185431365344188960782467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107655633948502341124173157 20185431365344188960782467)
              ·
                refine ⟨30278147048016283441173701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20185431365344188960782467 30278147048016283441173701)
                ·
                  refine ⟨5677152571503053145220069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30278147048016283441173701 5677152571503053145220069)
                  ·
                    refine ⟨1064466107156822464728763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5677152571503053145220069 1064466107156822464728763)
                    ·
                      rfl

theorem cell23_6219121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_6219121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219121 prefixEnd_6219121 := by exact prefixLift 6219121
  have htrace : WordTrace (prefixWord ++ tailWord_6219121) baseStart_6219121 baseEnd_6219121 := by
    simpa [prefixWord, tailWord_6219121, baseEnd_6219121] using wordTrace_append hprefix tailTrace_6219121
  have hstable : (prefixWord ++ tailWord_6219121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219121).length < 2 ^ (prefixWord ++ tailWord_6219121).sum := by decide
  have hdescent : baseEnd_6219121 < baseStart_6219121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219122 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6219122 : Nat := 118140960795 + 6219122 * 2 ^ 59
def prefixEnd_6219122 : Nat := 4983230072969 + 3 ^ 40 * 6219122 * 2
def baseEnd_6219122 : Nat := 3193398834951121890273785

theorem tailTrace_6219122 : CollatzResearch.WordTrace tailWord_6219122 prefixEnd_6219122 3193398834951121890273785 := by
  unfold tailWord_6219122
  simp only [CollatzResearch.WordTrace]
  refine ⟨56707503543797652580326905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151220009450127073547538413 56707503543797652580326905)
  ·
    refine ⟨42530627657848239435245179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56707503543797652580326905 42530627657848239435245179)
    ·
      refine ⟨63795941486772359152867769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42530627657848239435245179 63795941486772359152867769)
      ·
        refine ⟨47846956115079269364650827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63795941486772359152867769 47846956115079269364650827)
        ·
          refine ⟨71770434172618904046976241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47846956115079269364650827 71770434172618904046976241)
          ·
            refine ⟨53827825629464178035232181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71770434172618904046976241 53827825629464178035232181)
            ·
              refine ⟨5046358652762266690803017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53827825629464178035232181 5046358652762266690803017)
              ·
                refine ⟨3784768989571700018102263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5046358652762266690803017 3784768989571700018102263)
                ·
                  refine ⟨5677153484357550027153395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784768989571700018102263 5677153484357550027153395)
                  ·
                    refine ⟨8515730226536325040730093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5677153484357550027153395 8515730226536325040730093)
                    ·
                      refine ⟨3193398834951121890273785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515730226536325040730093 3193398834951121890273785)
                      ·
                        rfl

theorem cell23_6219122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6219122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219122 prefixEnd_6219122 := by exact prefixLift 6219122
  have htrace : WordTrace (prefixWord ++ tailWord_6219122) baseStart_6219122 baseEnd_6219122 := by
    simpa [prefixWord, tailWord_6219122, baseEnd_6219122] using wordTrace_append hprefix tailTrace_6219122
  have hstable : (prefixWord ++ tailWord_6219122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219122).length < 2 ^ (prefixWord ++ tailWord_6219122).sum := by decide
  have hdescent : baseEnd_6219122 < baseStart_6219122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219131 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3]
def baseStart_6219131 : Nat := 118140960795 + 6219131 * 2 ^ 59
def prefixEnd_6219131 : Nat := 4983230072969 + 3 ^ 40 * 6219131 * 2
def baseEnd_6219131 : Nat := 3193403456277012355061243

theorem tailTrace_6219131 : CollatzResearch.WordTrace tailWord_6219131 prefixEnd_6219131 3193403456277012355061243 := by
  unfold tailWord_6219131
  simp only [CollatzResearch.WordTrace]
  refine ⟨226830342432158004858385247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151220228288105336572256831 226830342432158004858385247)
  ·
    refine ⟨340245513648237007287577871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226830342432158004858385247 340245513648237007287577871)
    ·
      refine ⟨510368270472355510931366807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340245513648237007287577871 510368270472355510931366807)
      ·
        refine ⟨765552405708533266397050211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510368270472355510931366807 765552405708533266397050211)
        ·
          refine ⟨1148328608562799899595575317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765552405708533266397050211 1148328608562799899595575317)
          ·
            refine ⟨53827903526381245293542593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1148328608562799899595575317 53827903526381245293542593)
            ·
              refine ⟨40370927644785933970156945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53827903526381245293542593 40370927644785933970156945)
              ·
                refine ⟨30278195733589450477617709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40370927644785933970156945 30278195733589450477617709)
                ·
                  refine ⟨11354323400096043929106641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30278195733589450477617709 11354323400096043929106641)
                  ·
                    refine ⟨8515742550072032946829981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11354323400096043929106641 8515742550072032946829981)
                    ·
                      refine ⟨3193403456277012355061243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515742550072032946829981 3193403456277012355061243)
                      ·
                        rfl

theorem cell23_6219131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 3].length) (baseStart_6219131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219131 prefixEnd_6219131 := by exact prefixLift 6219131
  have htrace : WordTrace (prefixWord ++ tailWord_6219131) baseStart_6219131 baseEnd_6219131 := by
    simpa [prefixWord, tailWord_6219131, baseEnd_6219131] using wordTrace_append hprefix tailTrace_6219131
  have hstable : (prefixWord ++ tailWord_6219131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219131).length < 2 ^ (prefixWord ++ tailWord_6219131).sum := by decide
  have hdescent : baseEnd_6219131 < baseStart_6219131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219145 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_6219145 : Nat := 118140960795 + 6219145 * 2 ^ 59
def prefixEnd_6219145 : Nat := 4983230072969 + 3 ^ 40 * 6219145 * 2
def baseEnd_6219145 : Nat := 3193410645006175300286179

theorem tailTrace_6219145 : CollatzResearch.WordTrace tailWord_6219145 prefixEnd_6219145 3193410645006175300286179 := by
  unfold tailWord_6219145
  simp only [CollatzResearch.WordTrace]
  refine ⟨226830853054107285249394889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151220568702738190166263259 226830853054107285249394889)
  ·
    refine ⟨170123139790580463937046167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226830853054107285249394889 170123139790580463937046167)
    ·
      refine ⟨255184709685870695905569251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170123139790580463937046167 255184709685870695905569251)
      ·
        refine ⟨382777064528806043858353877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255184709685870695905569251 382777064528806043858353877)
        ·
          refine ⟨8971337449893891652930169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 382777064528806043858353877 8971337449893891652930169)
          ·
            refine ⟨6728503087420418739697627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8971337449893891652930169 6728503087420418739697627)
            ·
              refine ⟨10092754631130628109546441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728503087420418739697627 10092754631130628109546441)
              ·
                refine ⟨7569565973347971082159831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10092754631130628109546441 7569565973347971082159831)
                ·
                  refine ⟨11354348960021956623239747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569565973347971082159831 11354348960021956623239747)
                  ·
                    refine ⟨17031523440032934934859621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11354348960021956623239747 17031523440032934934859621)
                    ·
                      refine ⟨3193410645006175300286179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17031523440032934934859621 3193410645006175300286179)
                      ·
                        rfl

theorem cell23_6219145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_6219145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219145 prefixEnd_6219145 := by exact prefixLift 6219145
  have htrace : WordTrace (prefixWord ++ tailWord_6219145) baseStart_6219145 baseEnd_6219145 := by
    simpa [prefixWord, tailWord_6219145, baseEnd_6219145] using wordTrace_append hprefix tailTrace_6219145
  have hstable : (prefixWord ++ tailWord_6219145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219145).length < 2 ^ (prefixWord ++ tailWord_6219145).sum := by decide
  have hdescent : baseEnd_6219145 < baseStart_6219145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219161 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_6219161 : Nat := 118140960795 + 6219161 * 2 ^ 59
def prefixEnd_6219161 : Nat := 4983230072969 + 3 ^ 40 * 6219161 * 2
def baseEnd_6219161 : Nat := 3193418860696647237686105

theorem tailTrace_6219161 : CollatzResearch.WordTrace tailWord_6219161 prefixEnd_6219161 3193418860696647237686105 := by
  unfold tailWord_6219161
  simp only [CollatzResearch.WordTrace]
  refine ⟨226831436622049319981977337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151220957748032879987984891 226831436622049319981977337)
  ·
    refine ⟨170123577466536989986483003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226831436622049319981977337 170123577466536989986483003)
    ·
      refine ⟨255185366199805484979724505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170123577466536989986483003 255185366199805484979724505)
      ·
        refine ⟨191389024649854113734793379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255185366199805484979724505 191389024649854113734793379)
        ·
          refine ⟨287083536974781170602190069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191389024649854113734793379 287083536974781170602190069)
          ·
            refine ⟨26914081591385734743955319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287083536974781170602190069 26914081591385734743955319)
            ·
              refine ⟨40371122387078602115932979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26914081591385734743955319 40371122387078602115932979)
              ·
                refine ⟨60556683580617903173899469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40371122387078602115932979 60556683580617903173899469)
                ·
                  refine ⟨22708756342731713690212301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60556683580617903173899469 22708756342731713690212301)
                  ·
                    refine ⟨8515783628524392633829613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22708756342731713690212301 8515783628524392633829613)
                    ·
                      refine ⟨3193418860696647237686105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515783628524392633829613 3193418860696647237686105)
                      ·
                        rfl

theorem cell23_6219161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_6219161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219161 prefixEnd_6219161 := by exact prefixLift 6219161
  have htrace : WordTrace (prefixWord ++ tailWord_6219161) baseStart_6219161 baseEnd_6219161 := by
    simpa [prefixWord, tailWord_6219161, baseEnd_6219161] using wordTrace_append hprefix tailTrace_6219161
  have hstable : (prefixWord ++ tailWord_6219161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219161).length < 2 ^ (prefixWord ++ tailWord_6219161).sum := by decide
  have hdescent : baseEnd_6219161 < baseStart_6219161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219162 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2]
def baseStart_6219162 : Nat := 118140960795 + 6219162 * 2 ^ 59
def prefixEnd_6219162 : Nat := 4983230072969 + 3 ^ 40 * 6219162 * 2
def baseEnd_6219162 : Nat := 3193419374177301733773601

theorem tailTrace_6219162 : CollatzResearch.WordTrace tailWord_6219162 prefixEnd_6219162 3193419374177301733773601 := by
  unfold tailWord_6219162
  simp only [CollatzResearch.WordTrace]
  refine ⟨56707868273761424288190935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151220982063363798101842493 56707868273761424288190935)
  ·
    refine ⟨85061802410642136432286403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56707868273761424288190935 85061802410642136432286403)
    ·
      refine ⟨127592703615963204648429605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85061802410642136432286403 127592703615963204648429605)
      ·
        refine ⟨23923631927993100871580551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127592703615963204648429605 23923631927993100871580551)
        ·
          refine ⟨35885447891989651307370827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23923631927993100871580551 35885447891989651307370827)
          ·
            refine ⟨53828171837984476961056241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35885447891989651307370827 53828171837984476961056241)
            ·
              refine ⟨40371128878488357720792181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53828171837984476961056241 40371128878488357720792181)
              ·
                refine ⟨3784793332358283536324267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40371128878488357720792181 3784793332358283536324267)
                ·
                  refine ⟨5677189998537425304486401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784793332358283536324267 5677189998537425304486401)
                  ·
                    refine ⟨4257892498903068978364801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5677189998537425304486401 4257892498903068978364801)
                    ·
                      refine ⟨3193419374177301733773601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4257892498903068978364801 3193419374177301733773601)
                      ·
                        rfl

theorem cell23_6219162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_6219162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219162 prefixEnd_6219162 := by exact prefixLift 6219162
  have htrace : WordTrace (prefixWord ++ tailWord_6219162) baseStart_6219162 baseEnd_6219162 := by
    simpa [prefixWord, tailWord_6219162, baseEnd_6219162] using wordTrace_append hprefix tailTrace_6219162
  have hstable : (prefixWord ++ tailWord_6219162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219162).length < 2 ^ (prefixWord ++ tailWord_6219162).sum := by decide
  have hdescent : baseEnd_6219162 < baseStart_6219162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219221 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6219221 : Nat := 118140960795 + 6219221 * 2 ^ 59
def prefixEnd_6219221 : Nat := 4983230072969 + 3 ^ 40 * 6219221 * 2
def baseEnd_6219221 : Nat := 3193449669535917002935829

theorem tailTrace_6219221 : CollatzResearch.WordTrace tailWord_6219221 prefixEnd_6219221 3193449669535917002935829 := by
  unfold tailWord_6219221
  simp only [CollatzResearch.WordTrace]
  refine ⟨226833625001831950229161517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151222416667887966819441011 226833625001831950229161517)
  ·
    refine ⟨85062609375686981335935569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226833625001831950229161517 85062609375686981335935569)
    ·
      refine ⟨63796957031765236001951677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85062609375686981335935569 63796957031765236001951677)
      ·
        refine ⟨23923858886911963500731879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63796957031765236001951677 23923858886911963500731879)
        ·
          refine ⟨35885788330367945251097819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23923858886911963500731879 35885788330367945251097819)
          ·
            refine ⟨53828682495551917876646729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35885788330367945251097819 53828682495551917876646729)
            ·
              refine ⟨40371511871663938407485047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53828682495551917876646729 40371511871663938407485047)
              ·
                refine ⟨60557267807495907611227571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40371511871663938407485047 60557267807495907611227571)
                ·
                  refine ⟨90835901711243861416841357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60557267807495907611227571 90835901711243861416841357)
                  ·
                    refine ⟨34063463141716448031315509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90835901711243861416841357 34063463141716448031315509)
                    ·
                      refine ⟨3193449669535917002935829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34063463141716448031315509 3193449669535917002935829)
                      ·
                        rfl

theorem cell23_6219221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6219221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219221 prefixEnd_6219221 := by exact prefixLift 6219221
  have htrace : WordTrace (prefixWord ++ tailWord_6219221) baseStart_6219221 baseEnd_6219221 := by
    simpa [prefixWord, tailWord_6219221, baseEnd_6219221] using wordTrace_append hprefix tailTrace_6219221
  have hstable : (prefixWord ++ tailWord_6219221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219221).length < 2 ^ (prefixWord ++ tailWord_6219221).sum := by decide
  have hdescent : baseEnd_6219221 < baseStart_6219221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219231 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_6219231 : Nat := 118140960795 + 6219231 * 2 ^ 59
def prefixEnd_6219231 : Nat := 4983230072969 + 3 ^ 40 * 6219231 * 2
def baseEnd_6219231 : Nat := 3193454804342461963810783

theorem tailTrace_6219231 : CollatzResearch.WordTrace tailWord_6219231 prefixEnd_6219231 3193454804342461963810783 := by
  unfold tailWord_6219231
  simp only [CollatzResearch.WordTrace]
  refine ⟨226833989731795721937025547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151222659821197147958017031 226833989731795721937025547)
  ·
    refine ⟨340250984597693582905538321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226833989731795721937025547 340250984597693582905538321)
    ·
      refine ⟨255188238448270187179153741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340250984597693582905538321 255188238448270187179153741)
      ·
        refine ⟨95695589418101320192182653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255188238448270187179153741 95695589418101320192182653)
        ·
          refine ⟨35885846031787995072068495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95695589418101320192182653 35885846031787995072068495)
          ·
            refine ⟨53828769047681992608102743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35885846031787995072068495 53828769047681992608102743)
            ·
              refine ⟨80743153571522988912154115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53828769047681992608102743 80743153571522988912154115)
              ·
                refine ⟨121114730357284483368231173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80743153571522988912154115 121114730357284483368231173)
                ·
                  refine ⟨22709011941990840631543345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121114730357284483368231173 22709011941990840631543345)
                  ·
                    refine ⟨17031758956493130473657509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22709011941990840631543345 17031758956493130473657509)
                    ·
                      refine ⟨3193454804342461963810783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17031758956493130473657509 3193454804342461963810783)
                      ·
                        rfl

theorem cell23_6219231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_6219231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219231 prefixEnd_6219231 := by exact prefixLift 6219231
  have htrace : WordTrace (prefixWord ++ tailWord_6219231) baseStart_6219231 baseEnd_6219231 := by
    simpa [prefixWord, tailWord_6219231, baseEnd_6219231] using wordTrace_append hprefix tailTrace_6219231
  have hstable : (prefixWord ++ tailWord_6219231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219231).length < 2 ^ (prefixWord ++ tailWord_6219231).sum := by decide
  have hdescent : baseEnd_6219231 < baseStart_6219231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219251 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3]
def baseStart_6219251 : Nat := 118140960795 + 6219251 * 2 ^ 59
def prefixEnd_6219251 : Nat := 4983230072969 + 3 ^ 40 * 6219251 * 2
def baseEnd_6219251 : Nat := 3193465073955551885560691

theorem tailTrace_6219251 : CollatzResearch.WordTrace tailWord_6219251 prefixEnd_6219251 3193465073955551885560691 := by
  unfold tailWord_6219251
  simp only [CollatzResearch.WordTrace]
  refine ⟨226834719191723265352753607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151223146127815510235169071 226834719191723265352753607)
  ·
    refine ⟨340252078787584898029130411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226834719191723265352753607 340252078787584898029130411)
    ·
      refine ⟨510378118181377347043695617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340252078787584898029130411 510378118181377347043695617)
      ·
        refine ⟨382783588636033010282771713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510378118181377347043695617 382783588636033010282771713)
        ·
          refine ⟨287087691477024757712078785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382783588636033010282771713 287087691477024757712078785)
          ·
            refine ⟨215315768607768568284059089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287087691477024757712078785 215315768607768568284059089)
            ·
              refine ⟨161486826455826426213044317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215315768607768568284059089 161486826455826426213044317)
              ·
                refine ⟨60557559920934909829891619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161486826455826426213044317 60557559920934909829891619)
                ·
                  refine ⟨90836339881402364744837429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60557559920934909829891619 90836339881402364744837429)
                  ·
                    refine ⟨8515906863881471694828509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90836339881402364744837429 8515906863881471694828509)
                    ·
                      refine ⟨3193465073955551885560691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8515906863881471694828509 3193465073955551885560691)
                      ·
                        rfl

theorem cell23_6219251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_6219251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219251 prefixEnd_6219251 := by exact prefixLift 6219251
  have htrace : WordTrace (prefixWord ++ tailWord_6219251) baseStart_6219251 baseEnd_6219251 := by
    simpa [prefixWord, tailWord_6219251, baseEnd_6219251] using wordTrace_append hprefix tailTrace_6219251
  have hstable : (prefixWord ++ tailWord_6219251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219251).length < 2 ^ (prefixWord ++ tailWord_6219251).sum := by decide
  have hdescent : baseEnd_6219251 < baseStart_6219251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219281 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_6219281 : Nat := 118140960795 + 6219281 * 2 ^ 59
def prefixEnd_6219281 : Nat := 4983230072969 + 3 ^ 40 * 6219281 * 2
def baseEnd_6219281 : Nat := 3193480478375186768185553

theorem tailTrace_6219281 : CollatzResearch.WordTrace tailWord_6219281 prefixEnd_6219281 3193480478375186768185553 := by
  unfold tailWord_6219281
  simp only [CollatzResearch.WordTrace]
  refine ⟨226835813381614580476345697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151223875587743053650897131 226835813381614580476345697)
  ·
    refine ⟨170126860036210935357259273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226835813381614580476345697 170126860036210935357259273)
    ·
      refine ⟨127595145027158201517944455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170126860036210935357259273 127595145027158201517944455)
      ·
        refine ⟨191392717540737302276916683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127595145027158201517944455 191392717540737302276916683)
        ·
          refine ⟨287089076311105953415375025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191392717540737302276916683 287089076311105953415375025)
          ·
            refine ⟨215316807233329465061531269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287089076311105953415375025 215316807233329465061531269)
            ·
              refine ⟨40371901356249274699037113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215316807233329465061531269 40371901356249274699037113)
              ·
                refine ⟨30278926017186956024277835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40371901356249274699037113 30278926017186956024277835)
                ·
                  refine ⟨45418389025780434036416753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30278926017186956024277835 45418389025780434036416753)
                  ·
                    refine ⟨34063791769335325527312565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45418389025780434036416753 34063791769335325527312565)
                    ·
                      refine ⟨3193480478375186768185553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34063791769335325527312565 3193480478375186768185553)
                      ·
                        rfl

theorem cell23_6219281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_6219281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219281 prefixEnd_6219281 := by exact prefixLift 6219281
  have htrace : WordTrace (prefixWord ++ tailWord_6219281) baseStart_6219281 baseEnd_6219281 := by
    simpa [prefixWord, tailWord_6219281, baseEnd_6219281] using wordTrace_append hprefix tailTrace_6219281
  have hstable : (prefixWord ++ tailWord_6219281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219281).length < 2 ^ (prefixWord ++ tailWord_6219281).sum := by decide
  have hdescent : baseEnd_6219281 < baseStart_6219281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219371 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_6219371 : Nat := 118140960795 + 6219371 * 2 ^ 59
def prefixEnd_6219371 : Nat := 4983230072969 + 3 ^ 40 * 6219371 * 2
def baseEnd_6219371 : Nat := 3193526691634091416060139

theorem tailTrace_6219371 : CollatzResearch.WordTrace tailWord_6219371 prefixEnd_6219371 3193526691634091416060139 := by
  unfold tailWord_6219371
  simp only [CollatzResearch.WordTrace]
  refine ⟨226839095951288525847121967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151226063967525683898081311 226839095951288525847121967)
  ·
    refine ⟨340258643926932788770682951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226839095951288525847121967 340258643926932788770682951)
    ·
      refine ⟨510387965890399183156024427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340258643926932788770682951 510387965890399183156024427)
      ·
        refine ⟨765581948835598774734036641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510387965890399183156024427 765581948835598774734036641)
        ·
          refine ⟨574186461626699081050527481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765581948835598774734036641 574186461626699081050527481)
          ·
            refine ⟨430639846220024310787895611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574186461626699081050527481 430639846220024310787895611)
            ·
              refine ⟨645959769330036466181843417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430639846220024310787895611 645959769330036466181843417)
              ·
                refine ⟨484469826997527349636382563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645959769330036466181843417 484469826997527349636382563)
                ·
                  refine ⟨726704740496291024454573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484469826997527349636382563 726704740496291024454573845)
                  ·
                    refine ⟨34064284710763641771308149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 726704740496291024454573845 34064284710763641771308149)
                    ·
                      refine ⟨3193526691634091416060139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34064284710763641771308149 3193526691634091416060139)
                      ·
                        rfl

theorem cell23_6219371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_6219371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219371 prefixEnd_6219371 := by exact prefixLift 6219371
  have htrace : WordTrace (prefixWord ++ tailWord_6219371) baseStart_6219371 baseEnd_6219371 := by
    simpa [prefixWord, tailWord_6219371, baseEnd_6219371] using wordTrace_append hprefix tailTrace_6219371
  have hstable : (prefixWord ++ tailWord_6219371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219371).length < 2 ^ (prefixWord ++ tailWord_6219371).sum := by decide
  have hdescent : baseEnd_6219371 < baseStart_6219371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219385 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 5, 2]
def baseStart_6219385 : Nat := 118140960795 + 6219385 * 2 ^ 59
def prefixEnd_6219385 : Nat := 4983230072969 + 3 ^ 40 * 6219385 * 2
def baseEnd_6219385 : Nat := 3193533880363254361285075

theorem tailTrace_6219385 : CollatzResearch.WordTrace tailWord_6219385 prefixEnd_6219385 3193533880363254361285075 := by
  unfold tailWord_6219385
  simp only [CollatzResearch.WordTrace]
  refine ⟨226839606573237806238131609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151226404382158537492087739 226839606573237806238131609)
  ·
    refine ⟨170129704929928354678598707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226839606573237806238131609 170129704929928354678598707)
    ·
      refine ⟨255194557394892532017898061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170129704929928354678598707 255194557394892532017898061)
      ·
        refine ⟨95697959023084699506711773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255194557394892532017898061 95697959023084699506711773)
        ·
          refine ⟨35886734633656762315016915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95697959023084699506711773 35886734633656762315016915)
          ·
            refine ⟨53830101950485143472525373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35886734633656762315016915 53830101950485143472525373)
            ·
              refine ⟨20186288231431928802197015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53830101950485143472525373 20186288231431928802197015)
              ·
                refine ⟨30279432347147893203295523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20186288231431928802197015 30279432347147893203295523)
                ·
                  refine ⟨45419148520721839804943285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30279432347147893203295523 45419148520721839804943285)
                  ·
                    refine ⟨4258045173817672481713433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45419148520721839804943285 4258045173817672481713433)
                    ·
                      refine ⟨3193533880363254361285075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258045173817672481713433 3193533880363254361285075)
                      ·
                        rfl

theorem cell23_6219385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_6219385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219385 prefixEnd_6219385 := by exact prefixLift 6219385
  have htrace : WordTrace (prefixWord ++ tailWord_6219385) baseStart_6219385 baseEnd_6219385 := by
    simpa [prefixWord, tailWord_6219385, baseEnd_6219385] using wordTrace_append hprefix tailTrace_6219385
  have hstable : (prefixWord ++ tailWord_6219385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219385).length < 2 ^ (prefixWord ++ tailWord_6219385).sum := by decide
  have hdescent : baseEnd_6219385 < baseStart_6219385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219391 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 10]
def baseStart_6219391 : Nat := 118140960795 + 6219391 * 2 ^ 59
def prefixEnd_6219391 : Nat := 4983230072969 + 3 ^ 40 * 6219391 * 2
def baseEnd_6219391 : Nat := 1064512320415727112603349

theorem tailTrace_6219391 : CollatzResearch.WordTrace tailWord_6219391 prefixEnd_6219391 1064512320415727112603349 := by
  unfold tailWord_6219391
  simp only [CollatzResearch.WordTrace]
  refine ⟨226839825411216069262850027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151226550274144046175233351 226839825411216069262850027)
  ·
    refine ⟨340259738116824103894275041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226839825411216069262850027 340259738116824103894275041)
    ·
      refine ⟨255194803587618077920706281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340259738116824103894275041 255194803587618077920706281)
      ·
        refine ⟨191396102690713558440529711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255194803587618077920706281 191396102690713558440529711)
        ·
          refine ⟨287094154036070337660794567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191396102690713558440529711 287094154036070337660794567)
          ·
            refine ⟨430641231054105506491191851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287094154036070337660794567 430641231054105506491191851)
            ·
              refine ⟨645961846581158259736787777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430641231054105506491191851 645961846581158259736787777)
              ·
                refine ⟨484471384935868694802590833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645961846581158259736787777 484471384935868694802590833)
                ·
                  refine ⟨363353538701901521101943125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484471384935868694802590833 363353538701901521101943125)
                  ·
                    refine ⟨1064512320415727112603349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 363353538701901521101943125 1064512320415727112603349)
                    ·
                      rfl

theorem cell23_6219391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_6219391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219391 prefixEnd_6219391 := by exact prefixLift 6219391
  have htrace : WordTrace (prefixWord ++ tailWord_6219391) baseStart_6219391 baseEnd_6219391 := by
    simpa [prefixWord, tailWord_6219391, baseEnd_6219391] using wordTrace_append hprefix tailTrace_6219391
  have hstable : (prefixWord ++ tailWord_6219391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219391).length < 2 ^ (prefixWord ++ tailWord_6219391).sum := by decide
  have hdescent : baseEnd_6219391 < baseStart_6219391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219425 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_6219425 : Nat := 118140960795 + 6219425 * 2 ^ 59
def prefixEnd_6219425 : Nat := 4983230072969 + 3 ^ 40 * 6219425 * 2
def baseEnd_6219425 : Nat := 1064518139863144734928297

theorem tailTrace_6219425 : CollatzResearch.WordTrace tailWord_6219425 prefixEnd_6219425 1064518139863144734928297 := by
  unfold tailWord_6219425
  simp only [CollatzResearch.WordTrace]
  refine ⟨226841065493092893069587729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151227376995395262046391819 226841065493092893069587729)
  ·
    refine ⟨170130799119819669802190797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226841065493092893069587729 170130799119819669802190797)
    ·
      refine ⟨63799049669932376175821549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170130799119819669802190797 63799049669932376175821549)
      ·
        refine ⟨23924643626224641065933081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63799049669932376175821549 23924643626224641065933081)
        ·
          refine ⟨17943482719668480799449811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23924643626224641065933081 17943482719668480799449811)
          ·
            refine ⟨26915224079502721199174717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17943482719668480799449811 26915224079502721199174717)
            ·
              refine ⟨10093209029813520449690519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26915224079502721199174717 10093209029813520449690519)
              ·
                refine ⟨15139813544720280674535779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093209029813520449690519 15139813544720280674535779)
                ·
                  refine ⟨22709720317080421011803669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15139813544720280674535779 22709720317080421011803669)
                  ·
                    refine ⟨1064518139863144734928297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22709720317080421011803669 1064518139863144734928297)
                    ·
                      rfl

theorem cell23_6219425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_6219425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219425 prefixEnd_6219425 := by exact prefixLift 6219425
  have htrace : WordTrace (prefixWord ++ tailWord_6219425) baseStart_6219425 baseEnd_6219425 := by
    simpa [prefixWord, tailWord_6219425, baseEnd_6219425] using wordTrace_append hprefix tailTrace_6219425
  have hstable : (prefixWord ++ tailWord_6219425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219425).length < 2 ^ (prefixWord ++ tailWord_6219425).sum := by decide
  have hdescent : baseEnd_6219425 < baseStart_6219425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219452 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_6219452 : Nat := 118140960795 + 6219452 * 2 ^ 59
def prefixEnd_6219452 : Nat := 4983230072969 + 3 ^ 40 * 6219452 * 2
def baseEnd_6219452 : Nat := 3193568283567105599147267

theorem tailTrace_6219452 : CollatzResearch.WordTrace tailWord_6219452 prefixEnd_6219452 3193568283567105599147267 := by
  unfold tailWord_6219452
  simp only [CollatzResearch.WordTrace]
  refine ⟨113421025131997538340410305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151228033509330051120547073 113421025131997538340410305)
  ·
    refine ⟨85065768848998153755307729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113421025131997538340410305 85065768848998153755307729)
    ·
      refine ⟨63799326636748615316480797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85065768848998153755307729 63799326636748615316480797)
      ·
        refine ⟨23924747488780730743680299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63799326636748615316480797 23924747488780730743680299)
        ·
          refine ⟨35887121233171096115520449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23924747488780730743680299 35887121233171096115520449)
          ·
            refine ⟨26915340924878322086640337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35887121233171096115520449 26915340924878322086640337)
            ·
              refine ⟨20186505693658741564980253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26915340924878322086640337 20186505693658741564980253)
              ·
                refine ⟨7569939635122028086867595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20186505693658741564980253 7569939635122028086867595)
                ·
                  refine ⟨11354909452683042130301393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7569939635122028086867595 11354909452683042130301393)
                  ·
                    refine ⟨8516182089512281597726045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11354909452683042130301393 8516182089512281597726045)
                    ·
                      refine ⟨3193568283567105599147267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516182089512281597726045 3193568283567105599147267)
                      ·
                        rfl

theorem cell23_6219452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_6219452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219452 prefixEnd_6219452 := by exact prefixLift 6219452
  have htrace : WordTrace (prefixWord ++ tailWord_6219452) baseStart_6219452 baseEnd_6219452 := by
    simpa [prefixWord, tailWord_6219452, baseEnd_6219452] using wordTrace_append hprefix tailTrace_6219452
  have hstable : (prefixWord ++ tailWord_6219452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219452).length < 2 ^ (prefixWord ++ tailWord_6219452).sum := by decide
  have hdescent : baseEnd_6219452 < baseStart_6219452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219466 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_6219466 : Nat := 118140960795 + 6219466 * 2 ^ 59
def prefixEnd_6219466 : Nat := 4983230072969 + 3 ^ 40 * 6219466 * 2
def baseEnd_6219466 : Nat := 3193575472296268544372203

theorem tailTrace_6219466 : CollatzResearch.WordTrace tailWord_6219466 prefixEnd_6219466 3193575472296268544372203 := by
  unfold tailWord_6219466
  simp only [CollatzResearch.WordTrace]
  refine ⟨56710640221486089267957563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151228373923962904714553501 56710640221486089267957563)
  ·
    refine ⟨85065960332229133901936345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56710640221486089267957563 85065960332229133901936345)
    ·
      refine ⟨63799470249171850426452259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85065960332229133901936345 63799470249171850426452259)
      ·
        refine ⟨95699205373757775639678389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63799470249171850426452259 95699205373757775639678389)
        ·
          refine ⟨8971800503789791466219849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95699205373757775639678389 8971800503789791466219849)
          ·
            refine ⟨6728850377842343599664887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8971800503789791466219849 6728850377842343599664887)
            ·
              refine ⟨10093275566763515399497331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728850377842343599664887 10093275566763515399497331)
              ·
                refine ⟨15139913350145273099245997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093275566763515399497331 15139913350145273099245997)
                ·
                  refine ⟨5677467506304477412217249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15139913350145273099245997 5677467506304477412217249)
                  ·
                    refine ⟨4258100629728358059162937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5677467506304477412217249 4258100629728358059162937)
                    ·
                      refine ⟨3193575472296268544372203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258100629728358059162937 3193575472296268544372203)
                      ·
                        rfl

theorem cell23_6219466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_6219466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219466 prefixEnd_6219466 := by exact prefixLift 6219466
  have htrace : WordTrace (prefixWord ++ tailWord_6219466) baseStart_6219466 baseEnd_6219466 := by
    simpa [prefixWord, tailWord_6219466, baseEnd_6219466] using wordTrace_append hprefix tailTrace_6219466
  have hstable : (prefixWord ++ tailWord_6219466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219466).length < 2 ^ (prefixWord ++ tailWord_6219466).sum := by decide
  have hdescent : baseEnd_6219466 < baseStart_6219466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219476 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_6219476 : Nat := 118140960795 + 6219476 * 2 ^ 59
def prefixEnd_6219476 : Nat := 4983230072969 + 3 ^ 40 * 6219476 * 2
def baseEnd_6219476 : Nat := 1064526869034271168415719

theorem tailTrace_6219476 : CollatzResearch.WordTrace tailWord_6219476 prefixEnd_6219476 1064526869034271168415719 := by
  unfold tailWord_6219476
  simp only [CollatzResearch.WordTrace]
  refine ⟨113421462807954064389847141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151228617077272085853129521 113421462807954064389847141)
  ·
    refine ⟨21266524276491387073096339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113421462807954064389847141 21266524276491387073096339)
    ·
      refine ⟨31899786414737080609644509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21266524276491387073096339 31899786414737080609644509)
      ·
        refine ⟨11962419905526405228616691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31899786414737080609644509 11962419905526405228616691)
        ·
          refine ⟨17943629858289607842925037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11962419905526405228616691 17943629858289607842925037)
          ·
            refine ⟨6728861196858602941096889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17943629858289607842925037 6728861196858602941096889)
            ·
              refine ⟨5046645897643952205822667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6728861196858602941096889 5046645897643952205822667)
              ·
                refine ⟨7569968846465928308734001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5046645897643952205822667 7569968846465928308734001)
                ·
                  refine ⟨5677476634849446231550501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7569968846465928308734001 5677476634849446231550501)
                  ·
                    refine ⟨1064526869034271168415719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5677476634849446231550501 1064526869034271168415719)
                    ·
                      rfl

theorem cell23_6219476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_6219476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219476 prefixEnd_6219476 := by exact prefixLift 6219476
  have htrace : WordTrace (prefixWord ++ tailWord_6219476) baseStart_6219476 baseEnd_6219476 := by
    simpa [prefixWord, tailWord_6219476, baseEnd_6219476] using wordTrace_append hprefix tailTrace_6219476
  have hstable : (prefixWord ++ tailWord_6219476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219476).length < 2 ^ (prefixWord ++ tailWord_6219476).sum := by decide
  have hdescent : baseEnd_6219476 < baseStart_6219476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219492 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_6219492 : Nat := 118140960795 + 6219492 * 2 ^ 59
def prefixEnd_6219492 : Nat := 4983230072969 + 3 ^ 40 * 6219492 * 2
def baseEnd_6219492 : Nat := 3193588822793285442647083

theorem tailTrace_6219492 : CollatzResearch.WordTrace tailWord_6219492 prefixEnd_6219492 3193588822793285442647083 := by
  unfold tailWord_6219492
  simp only [CollatzResearch.WordTrace]
  refine ⟨113421754591925081756138365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151229006122566775674851153 113421754591925081756138365)
  ·
    refine ⟨42533157971971905658551887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113421754591925081756138365 42533157971971905658551887)
    ·
      refine ⟨63799736957957858487827831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42533157971971905658551887 63799736957957858487827831)
      ·
        refine ⟨95699605436936787731741747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63799736957957858487827831 95699605436936787731741747)
        ·
          refine ⟨143549408155405181597612621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95699605436936787731741747 143549408155405181597612621)
          ·
            refine ⟨53831028058276943099104733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143549408155405181597612621 53831028058276943099104733)
            ·
              refine ⟨20186635521853853662164275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53831028058276943099104733 20186635521853853662164275)
              ·
                refine ⟨30279953282780780493246413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20186635521853853662164275 30279953282780780493246413)
                ·
                  refine ⟨11354982481042792684967405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30279953282780780493246413 11354982481042792684967405)
                  ·
                    refine ⟨4258118430391047256862777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11354982481042792684967405 4258118430391047256862777)
                    ·
                      refine ⟨3193588822793285442647083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258118430391047256862777 3193588822793285442647083)
                      ·
                        rfl

theorem cell23_6219492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_6219492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219492 prefixEnd_6219492 := by exact prefixLift 6219492
  have htrace : WordTrace (prefixWord ++ tailWord_6219492) baseStart_6219492 baseEnd_6219492 := by
    simpa [prefixWord, tailWord_6219492, baseEnd_6219492] using wordTrace_append hprefix tailTrace_6219492
  have hstable : (prefixWord ++ tailWord_6219492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219492).length < 2 ^ (prefixWord ++ tailWord_6219492).sum := by decide
  have hdescent : baseEnd_6219492 < baseStart_6219492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219573 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_6219573 : Nat := 118140960795 + 6219573 * 2 ^ 59
def prefixEnd_6219573 : Nat := 4983230072969 + 3 ^ 40 * 6219573 * 2
def baseEnd_6219573 : Nat := 3193630414726299625734211

theorem tailTrace_6219573 : CollatzResearch.WordTrace tailWord_6219573 prefixEnd_6219573 3193630414726299625734211 := by
  unfold tailWord_6219573
  simp only [CollatzResearch.WordTrace]
  refine ⟨226846463496556714345975373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151230975664371142897316915 226846463496556714345975373)
  ·
    refine ⟨85067423811208767879740765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226846463496556714345975373 85067423811208767879740765)
    ·
      refine ⟨31900283929203287954902787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85067423811208767879740765 31900283929203287954902787)
      ·
        refine ⟨47850425893804931932354181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31900283929203287954902787 47850425893804931932354181)
        ·
          refine ⟨8971954855088424737316409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47850425893804931932354181 8971954855088424737316409)
          ·
            refine ⟨6728966141316318552987307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8971954855088424737316409 6728966141316318552987307)
            ·
              refine ⟨10093449211974477829480961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6728966141316318552987307 10093449211974477829480961)
              ·
                refine ⟨7570086908980858372110721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10093449211974477829480961 7570086908980858372110721)
                ·
                  refine ⟨5677565181735643779083041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7570086908980858372110721 5677565181735643779083041)
                  ·
                    refine ⟨4258173886301732834312281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5677565181735643779083041 4258173886301732834312281)
                    ·
                      refine ⟨3193630414726299625734211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258173886301732834312281 3193630414726299625734211)
                      ·
                        rfl

theorem cell23_6219573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_6219573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219573 prefixEnd_6219573 := by exact prefixLift 6219573
  have htrace : WordTrace (prefixWord ++ tailWord_6219573) baseStart_6219573 baseEnd_6219573 := by
    simpa [prefixWord, tailWord_6219573, baseEnd_6219573] using wordTrace_append hprefix tailTrace_6219573
  have hstable : (prefixWord ++ tailWord_6219573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219573).length < 2 ^ (prefixWord ++ tailWord_6219573).sum := by decide
  have hdescent : baseEnd_6219573 < baseStart_6219573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219635 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 6]
def baseStart_6219635 : Nat := 118140960795 + 6219635 * 2 ^ 59
def prefixEnd_6219635 : Nat := 4983230072969 + 3 ^ 40 * 6219635 * 2
def baseEnd_6219635 : Nat := 354851361169653153684325

theorem tailTrace_6219635 : CollatzResearch.WordTrace tailWord_6219635 prefixEnd_6219635 354851361169653153684325 := by
  unfold tailWord_6219635
  simp only [CollatzResearch.WordTrace]
  refine ⟨226848724822332098934732359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151232483214888065956488239 226848724822332098934732359)
  ·
    refine ⟨340273087233498148402098539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226848724822332098934732359 340273087233498148402098539)
    ·
      refine ⟨510409630850247222603147809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340273087233498148402098539 510409630850247222603147809)
      ·
        refine ⟨382807223137685416952360857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510409630850247222603147809 382807223137685416952360857)
        ·
          refine ⟨287105417353264062714270643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382807223137685416952360857 287105417353264062714270643)
          ·
            refine ⟨430658126029896094071405965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287105417353264062714270643 430658126029896094071405965)
            ·
              refine ⟨161496797261211035276777237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 430658126029896094071405965 161496797261211035276777237)
              ·
                refine ⟨7570162371619267278598933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161496797261211035276777237 7570162371619267278598933)
                ·
                  refine ⟨354851361169653153684325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7570162371619267278598933 354851361169653153684325)
                  ·
                    rfl

theorem cell23_6219635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 6].length) (baseStart_6219635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219635 prefixEnd_6219635 := by exact prefixLift 6219635
  have htrace : WordTrace (prefixWord ++ tailWord_6219635) baseStart_6219635 baseEnd_6219635 := by
    simpa [prefixWord, tailWord_6219635, baseEnd_6219635] using wordTrace_append hprefix tailTrace_6219635
  have hstable : (prefixWord ++ tailWord_6219635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219635).length < 2 ^ (prefixWord ++ tailWord_6219635).sum := by decide
  have hdescent : baseEnd_6219635 < baseStart_6219635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219666 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6219666 : Nat := 118140960795 + 6219666 * 2 ^ 59
def prefixEnd_6219666 : Nat := 4983230072969 + 3 ^ 40 * 6219666 * 2
def baseEnd_6219666 : Nat := 3193678168427167761871283

theorem tailTrace_6219666 : CollatzResearch.WordTrace tailWord_6219666 prefixEnd_6219666 3193678168427167761871283 := by
  unfold tailWord_6219666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56712463871304947807277713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151233236990146527486073901 56712463871304947807277713)
  ·
    refine ⟨42534347903478710855458285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56712463871304947807277713 42534347903478710855458285)
    ·
      refine ⟨15950380463804516570796857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42534347903478710855458285 15950380463804516570796857)
      ·
        refine ⟨11962785347853387428097643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15950380463804516570796857 11962785347853387428097643)
        ·
          refine ⟨17944178021780081142146465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11962785347853387428097643 17944178021780081142146465)
          ·
            refine ⟨13458133516335060856609849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17944178021780081142146465 13458133516335060856609849)
            ·
              refine ⟨10093600137251295642457387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13458133516335060856609849 10093600137251295642457387)
              ·
                refine ⟨15140400205876943463686081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093600137251295642457387 15140400205876943463686081)
                ·
                  refine ⟨11355300154407707597764561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15140400205876943463686081 11355300154407707597764561)
                  ·
                    refine ⟨8516475115805780698323421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11355300154407707597764561 8516475115805780698323421)
                    ·
                      refine ⟨3193678168427167761871283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516475115805780698323421 3193678168427167761871283)
                      ·
                        rfl

theorem cell23_6219666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6219666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219666 prefixEnd_6219666 := by exact prefixLift 6219666
  have htrace : WordTrace (prefixWord ++ tailWord_6219666) baseStart_6219666 baseEnd_6219666 := by
    simpa [prefixWord, tailWord_6219666, baseEnd_6219666] using wordTrace_append hprefix tailTrace_6219666
  have hstable : (prefixWord ++ tailWord_6219666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219666).length < 2 ^ (prefixWord ++ tailWord_6219666).sum := by decide
  have hdescent : baseEnd_6219666 < baseStart_6219666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219695 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 3, 6]
def baseStart_6219695 : Nat := 118140960795 + 6219695 * 2 ^ 59
def prefixEnd_6219695 : Nat := 4983230072969 + 3 ^ 40 * 6219695 * 2
def baseEnd_6219695 : Nat := 1064564353122049382802883

theorem tailTrace_6219695 : CollatzResearch.WordTrace tailWord_6219695 prefixEnd_6219695 1064564353122049382802883 := by
  unfold tailWord_6219695
  simp only [CollatzResearch.WordTrace]
  refine ⟨226850913202114729181916539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151233942134743152787944359 226850913202114729181916539)
  ·
    refine ⟨340276369803172093772874809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226850913202114729181916539 340276369803172093772874809)
    ·
      refine ⟨255207277352379070329656107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340276369803172093772874809 255207277352379070329656107)
      ·
        refine ⟨382810916028568605494484161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255207277352379070329656107 382810916028568605494484161)
        ·
          refine ⟨287108187021426454120863121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382810916028568605494484161 287108187021426454120863121)
          ·
            refine ⟨215331140266069840590647341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287108187021426454120863121 215331140266069840590647341)
            ·
              refine ⟨80749177599776190221492753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215331140266069840590647341 80749177599776190221492753)
              ·
                refine ⟨60561883199832142666119565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80749177599776190221492753 60561883199832142666119565)
                ·
                  refine ⟨22710706199937053499794837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60561883199832142666119565 22710706199937053499794837)
                  ·
                    refine ⟨1064564353122049382802883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22710706199937053499794837 1064564353122049382802883)
                    ·
                      rfl

theorem cell23_6219695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_6219695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219695 prefixEnd_6219695 := by exact prefixLift 6219695
  have htrace : WordTrace (prefixWord ++ tailWord_6219695) baseStart_6219695 baseEnd_6219695 := by
    simpa [prefixWord, tailWord_6219695, baseEnd_6219695] using wordTrace_append hprefix tailTrace_6219695
  have hstable : (prefixWord ++ tailWord_6219695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219695).length < 2 ^ (prefixWord ++ tailWord_6219695).sum := by decide
  have hdescent : baseEnd_6219695 < baseStart_6219695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219712 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_6219712 : Nat := 118140960795 + 6219712 * 2 ^ 59
def prefixEnd_6219712 : Nat := 4983230072969 + 3 ^ 40 * 6219712 * 2
def baseEnd_6219712 : Nat := 1064567262845758193965357

theorem tailTrace_6219712 : CollatzResearch.WordTrace tailWord_6219712 prefixEnd_6219712 1064567262845758193965357 := by
  unfold tailWord_6219712
  simp only [CollatzResearch.WordTrace]
  refine ⟨113425766621526570542642695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151234355495368760723523593 113425766621526570542642695)
  ·
    refine ⟨170138649932289855813964043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113425766621526570542642695 170138649932289855813964043)
    ·
      refine ⟨255207974898434783720946065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170138649932289855813964043 255207974898434783720946065)
      ·
        refine ⟨191405981173826087790709549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255207974898434783720946065 191405981173826087790709549)
        ·
          refine ⟨71777242940184782921516081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191405981173826087790709549 71777242940184782921516081)
          ·
            refine ⟨53832932205138587191137061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71777242940184782921516081 53832932205138587191137061)
            ·
              refine ⟨10093674788463485098338199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53832932205138587191137061 10093674788463485098338199)
              ·
                refine ⟨15140512182695227647507299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093674788463485098338199 15140512182695227647507299)
                ·
                  refine ⟨22710768274042841471260949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15140512182695227647507299 22710768274042841471260949)
                  ·
                    refine ⟨1064567262845758193965357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22710768274042841471260949 1064567262845758193965357)
                    ·
                      rfl

theorem cell23_6219712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_6219712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219712 prefixEnd_6219712 := by exact prefixLift 6219712
  have htrace : WordTrace (prefixWord ++ tailWord_6219712) baseStart_6219712 baseEnd_6219712 := by
    simpa [prefixWord, tailWord_6219712, baseEnd_6219712] using wordTrace_append hprefix tailTrace_6219712
  have hstable : (prefixWord ++ tailWord_6219712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219712).length < 2 ^ (prefixWord ++ tailWord_6219712).sum := by decide
  have hdescent : baseEnd_6219712 < baseStart_6219712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219730 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6219730 : Nat := 118140960795 + 6219730 * 2 ^ 59
def prefixEnd_6219730 : Nat := 4983230072969 + 3 ^ 40 * 6219730 * 2
def baseEnd_6219730 : Nat := 3193711031189055511470989

theorem tailTrace_6219730 : CollatzResearch.WordTrace tailWord_6219730 prefixEnd_6219730 3193711031189055511470989 := by
  unfold tailWord_6219730
  simp only [CollatzResearch.WordTrace]
  refine ⟨56713047439246982539860161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151234793171325286772960429 56713047439246982539860161)
  ·
    refine ⟨42534785579435236904895121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56713047439246982539860161 42534785579435236904895121)
    ·
      refine ⟨31901089184576427678671341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42534785579435236904895121 31901089184576427678671341)
      ·
        refine ⟨11962908444216160379501753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31901089184576427678671341 11962908444216160379501753)
        ·
          refine ⟨8972181333162120284626315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11962908444216160379501753 8972181333162120284626315)
          ·
            refine ⟨13458271999743180426939473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972181333162120284626315 13458271999743180426939473)
            ·
              refine ⟨10093703999807385320204605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13458271999743180426939473 10093703999807385320204605)
              ·
                refine ⟨3785138999927769495076727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10093703999807385320204605 3785138999927769495076727)
                ·
                  refine ⟨5677708499891654242615091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785138999927769495076727 5677708499891654242615091)
                  ·
                    refine ⟨8516562749837481363922637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5677708499891654242615091 8516562749837481363922637)
                    ·
                      refine ⟨3193711031189055511470989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516562749837481363922637 3193711031189055511470989)
                      ·
                        rfl

theorem cell23_6219730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6219730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219730 prefixEnd_6219730 := by exact prefixLift 6219730
  have htrace : WordTrace (prefixWord ++ tailWord_6219730) baseStart_6219730 baseEnd_6219730 := by
    simpa [prefixWord, tailWord_6219730, baseEnd_6219730] using wordTrace_append hprefix tailTrace_6219730
  have hstable : (prefixWord ++ tailWord_6219730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219730).length < 2 ^ (prefixWord ++ tailWord_6219730).sum := by decide
  have hdescent : baseEnd_6219730 < baseStart_6219730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219755 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 9]
def baseStart_6219755 : Nat := 118140960795 + 6219755 * 2 ^ 59
def prefixEnd_6219755 : Nat := 4983230072969 + 3 ^ 40 * 6219755 * 2
def baseEnd_6219755 : Nat := 1064574622735139304552791

theorem tailTrace_6219755 : CollatzResearch.WordTrace tailWord_6219755 prefixEnd_6219755 1064574622735139304552791 := by
  unfold tailWord_6219755
  simp only [CollatzResearch.WordTrace]
  refine ⟨226853101581897359429100719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151235401054598239619400479 226853101581897359429100719)
  ·
    refine ⟨340279652372846039143651079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226853101581897359429100719 340279652372846039143651079)
    ·
      refine ⟨510419478559269058715476619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340279652372846039143651079 510419478559269058715476619)
      ·
        refine ⟨765629217838903588073214929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510419478559269058715476619 765629217838903588073214929)
        ·
          refine ⟨574221913379177691054911197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765629217838903588073214929 574221913379177691054911197)
          ·
            refine ⟨215333217517191634145591699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574221913379177691054911197 215333217517191634145591699)
            ·
              refine ⟨322999826275787451218387549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215333217517191634145591699 322999826275787451218387549)
              ·
                refine ⟨121124934853420294206895331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322999826275787451218387549 121124934853420294206895331)
                ·
                  refine ⟨181687402280130441310342997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121124934853420294206895331 181687402280130441310342997)
                  ·
                    refine ⟨1064574622735139304552791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181687402280130441310342997 1064574622735139304552791)
                    ·
                      rfl

theorem cell23_6219755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_6219755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219755 prefixEnd_6219755 := by exact prefixLift 6219755
  have htrace : WordTrace (prefixWord ++ tailWord_6219755) baseStart_6219755 baseEnd_6219755 := by
    simpa [prefixWord, tailWord_6219755, baseEnd_6219755] using wordTrace_append hprefix tailTrace_6219755
  have hstable : (prefixWord ++ tailWord_6219755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219755).length < 2 ^ (prefixWord ++ tailWord_6219755).sum := by decide
  have hdescent : baseEnd_6219755 < baseStart_6219755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219769 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_6219769 : Nat := 118140960795 + 6219769 * 2 ^ 59
def prefixEnd_6219769 : Nat := 4983230072969 + 3 ^ 40 * 6219769 * 2
def baseEnd_6219769 : Nat := 3193731056934580858883309

theorem tailTrace_6219769 : CollatzResearch.WordTrace tailWord_6219769 prefixEnd_6219769 3193731056934580858883309 := by
  unfold tailWord_6219769
  simp only [CollatzResearch.WordTrace]
  refine ⟨226853612203846639820110361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151235741469231093213406907 226853612203846639820110361)
  ·
    refine ⟨170140209152884979865082771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226853612203846639820110361 170140209152884979865082771)
    ·
      refine ⟨255210313729327469797624157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170140209152884979865082771 255210313729327469797624157)
      ·
        refine ⟨95703867648497801174109059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255210313729327469797624157 95703867648497801174109059)
        ·
          refine ⟨143555801472746701761163589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95703867648497801174109059 143555801472746701761163589)
          ·
            refine ⟨26916712776140006580218173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143555801472746701761163589 26916712776140006580218173)
            ·
              refine ⟨10093767291052502467581815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26916712776140006580218173 10093767291052502467581815)
              ·
                refine ⟨15140650936578753701372723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10093767291052502467581815 15140650936578753701372723)
                ·
                  refine ⟨22710976404868130552059085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15140650936578753701372723 22710976404868130552059085)
                  ·
                    refine ⟨8516616151825548957022157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22710976404868130552059085 8516616151825548957022157)
                    ·
                      refine ⟨3193731056934580858883309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516616151825548957022157 3193731056934580858883309)
                      ·
                        rfl

theorem cell23_6219769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_6219769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219769 prefixEnd_6219769 := by exact prefixLift 6219769
  have htrace : WordTrace (prefixWord ++ tailWord_6219769) baseStart_6219769 baseEnd_6219769 := by
    simpa [prefixWord, tailWord_6219769, baseEnd_6219769] using wordTrace_append hprefix tailTrace_6219769
  have hstable : (prefixWord ++ tailWord_6219769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219769).length < 2 ^ (prefixWord ++ tailWord_6219769).sum := by decide
  have hdescent : baseEnd_6219769 < baseStart_6219769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219779 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 3, 3, 2]
def baseStart_6219779 : Nat := 118140960795 + 6219779 * 2 ^ 59
def prefixEnd_6219779 : Nat := 4983230072969 + 3 ^ 40 * 6219779 * 2
def baseEnd_6219779 : Nat := 3193736191741125819758263

theorem tailTrace_6219779 : CollatzResearch.WordTrace tailWord_6219779 prefixEnd_6219779 3193736191741125819758263 := by
  unfold tailWord_6219779
  simp only [CollatzResearch.WordTrace]
  refine ⟨226853976933810411527974391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151235984622540274351982927 226853976933810411527974391)
  ·
    refine ⟨340280965400715617291961587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226853976933810411527974391 340280965400715617291961587)
    ·
      refine ⟨510421448101073425937942381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340280965400715617291961587 510421448101073425937942381)
      ·
        refine ⟨191408043037902534726728393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510421448101073425937942381 191408043037902534726728393)
        ·
          refine ⟨143556032278426901045046295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191408043037902534726728393 143556032278426901045046295)
          ·
            refine ⟨215334048417640351567569443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143556032278426901045046295 215334048417640351567569443)
            ·
              refine ⟨323001072626460527351354165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215334048417640351567569443 323001072626460527351354165)
              ·
                refine ⟨30281350558730674439189453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323001072626460527351354165 30281350558730674439189453)
                ·
                  refine ⟨11355506459524002914696045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30281350558730674439189453 11355506459524002914696045)
                  ·
                    refine ⟨4258314922321501093011017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11355506459524002914696045 4258314922321501093011017)
                    ·
                      refine ⟨3193736191741125819758263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258314922321501093011017 3193736191741125819758263)
                      ·
                        rfl

theorem cell23_6219779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_6219779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219779 prefixEnd_6219779 := by exact prefixLift 6219779
  have htrace : WordTrace (prefixWord ++ tailWord_6219779) baseStart_6219779 baseEnd_6219779 := by
    simpa [prefixWord, tailWord_6219779, baseEnd_6219779] using wordTrace_append hprefix tailTrace_6219779
  have hstable : (prefixWord ++ tailWord_6219779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219779).length < 2 ^ (prefixWord ++ tailWord_6219779).sum := by decide
  have hdescent : baseEnd_6219779 < baseStart_6219779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219846 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6219846 : Nat := 118140960795 + 6219846 * 2 ^ 59
def prefixEnd_6219846 : Nat := 4983230072969 + 3 ^ 40 * 6219846 * 2
def baseEnd_6219846 : Nat := 3193770594944977057620455

theorem tailTrace_6219846 : CollatzResearch.WordTrace tailWord_6219846 prefixEnd_6219846 3193770594944977057620455 := by
  unfold tailWord_6219846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7089263144517740061583231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151237613749711787980442261 7089263144517740061583231)
  ·
    refine ⟨10633894716776610092374847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7089263144517740061583231 10633894716776610092374847)
    ·
      refine ⟨15950842075164915138562271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10633894716776610092374847 15950842075164915138562271)
      ·
        refine ⟨23926263112747372707843407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15950842075164915138562271 23926263112747372707843407)
        ·
          refine ⟨35889394669121059061765111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23926263112747372707843407 35889394669121059061765111)
          ·
            refine ⟨53834092003681588592647667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35889394669121059061765111 53834092003681588592647667)
            ·
              refine ⟨80751138005522382888971501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53834092003681588592647667 80751138005522382888971501)
              ·
                refine ⟨30281676752070893583364313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80751138005522382888971501 30281676752070893583364313)
                ·
                  refine ⟨22711257564053170187523235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30281676752070893583364313 22711257564053170187523235)
                  ·
                    refine ⟨34066886346079755281284853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22711257564053170187523235 34066886346079755281284853)
                    ·
                      refine ⟨3193770594944977057620455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34066886346079755281284853 3193770594944977057620455)
                      ·
                        rfl

theorem cell23_6219846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6219846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219846 prefixEnd_6219846 := by exact prefixLift 6219846
  have htrace : WordTrace (prefixWord ++ tailWord_6219846) baseStart_6219846 baseEnd_6219846 := by
    simpa [prefixWord, tailWord_6219846, baseEnd_6219846] using wordTrace_append hprefix tailTrace_6219846
  have hstable : (prefixWord ++ tailWord_6219846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219846).length < 2 ^ (prefixWord ++ tailWord_6219846).sum := by decide
  have hdescent : baseEnd_6219846 < baseStart_6219846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219849 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 5]
def baseStart_6219849 : Nat := 118140960795 + 6219849 * 2 ^ 59
def prefixEnd_6219849 : Nat := 4983230072969 + 3 ^ 40 * 6219849 * 2
def baseEnd_6219849 : Nat := 354863570598548949542549

theorem tailTrace_6219849 : CollatzResearch.WordTrace tailWord_6219849 prefixEnd_6219849 354863570598548949542549 := by
  unfold tailWord_6219849
  simp only [CollatzResearch.WordTrace]
  refine ⟨226856530043556813483022601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151237686695704542322015067 226856530043556813483022601)
  ·
    refine ⟨170142397532667610112266951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226856530043556813483022601 170142397532667610112266951)
    ·
      refine ⟨255213596299001415168400427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170142397532667610112266951 255213596299001415168400427)
      ·
        refine ⟨382820394448502122752600641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255213596299001415168400427 382820394448502122752600641)
        ·
          refine ⟨287115295836376592064450481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382820394448502122752600641 287115295836376592064450481)
          ·
            refine ⟨215336471877282444048337861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287115295836376592064450481 215336471877282444048337861)
            ·
              refine ⟨40375588476990458259063349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215336471877282444048337861 40375588476990458259063349)
              ·
                refine ⟨3785211419717855461787189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40375588476990458259063349 3785211419717855461787189)
                ·
                  refine ⟨354863570598548949542549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3785211419717855461787189 354863570598548949542549)
                  ·
                    rfl

theorem cell23_6219849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 5].length) (baseStart_6219849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219849 prefixEnd_6219849 := by exact prefixLift 6219849
  have htrace : WordTrace (prefixWord ++ tailWord_6219849) baseStart_6219849 baseEnd_6219849 := by
    simpa [prefixWord, tailWord_6219849, baseEnd_6219849] using wordTrace_append hprefix tailTrace_6219849
  have hstable : (prefixWord ++ tailWord_6219849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219849).length < 2 ^ (prefixWord ++ tailWord_6219849).sum := by decide
  have hdescent : baseEnd_6219849 < baseStart_6219849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219886 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_6219886 : Nat := 118140960795 + 6219886 * 2 ^ 59
def prefixEnd_6219886 : Nat := 4983230072969 + 3 ^ 40 * 6219886 * 2
def baseEnd_6219886 : Nat := 3193791134171156901120271

theorem tailTrace_6219886 : CollatzResearch.WordTrace tailWord_6219886 prefixEnd_6219886 3193791134171156901120271 := by
  unfold tailWord_6219886
  simp only [CollatzResearch.WordTrace]
  refine ⟨28357234943052846100264939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151238586362948512534746341 28357234943052846100264939)
  ·
    refine ⟨42535852414579269150397409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28357234943052846100264939 42535852414579269150397409)
    ·
      refine ⟨31901889310934451862798057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42535852414579269150397409 31901889310934451862798057)
      ·
        refine ⟨23926416983200838897098543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31901889310934451862798057 23926416983200838897098543)
        ·
          refine ⟨35889625474801258345647815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23926416983200838897098543 35889625474801258345647815)
          ·
            refine ⟨53834438212201887518471723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35889625474801258345647815 53834438212201887518471723)
            ·
              refine ⟨80751657318302831277707585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53834438212201887518471723 80751657318302831277707585)
              ·
                refine ⟨60563742988727123458280689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80751657318302831277707585 60563742988727123458280689)
                ·
                  refine ⟨45422807241545342593710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60563742988727123458280689 45422807241545342593710517)
                  ·
                    refine ⟨4258388178894875868160361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45422807241545342593710517 4258388178894875868160361)
                    ·
                      refine ⟨3193791134171156901120271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258388178894875868160361 3193791134171156901120271)
                      ·
                        rfl

theorem cell23_6219886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_6219886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219886 prefixEnd_6219886 := by exact prefixLift 6219886
  have htrace : WordTrace (prefixWord ++ tailWord_6219886) baseStart_6219886 baseEnd_6219886 := by
    simpa [prefixWord, tailWord_6219886, baseEnd_6219886] using wordTrace_append hprefix tailTrace_6219886
  have hstable : (prefixWord ++ tailWord_6219886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219886).length < 2 ^ (prefixWord ++ tailWord_6219886).sum := by decide
  have hdescent : baseEnd_6219886 < baseStart_6219886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219970 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6219970 : Nat := 118140960795 + 6219970 * 2 ^ 59
def prefixEnd_6219970 : Nat := 4983230072969 + 3 ^ 40 * 6219970 * 2
def baseEnd_6219970 : Nat := 3193834266546134572469885

theorem tailTrace_6219970 : CollatzResearch.WordTrace tailWord_6219970 prefixEnd_6219970 3193834266546134572469885 := by
  unfold tailWord_6219970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56715235819029612787044341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151240628850745634098784909 56715235819029612787044341)
  ·
    refine ⟨5317053358034026198785407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56715235819029612787044341 5317053358034026198785407)
    ·
      refine ⟨7975580037051039298178111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5317053358034026198785407 7975580037051039298178111)
      ·
        refine ⟨11963370055576558947267167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975580037051039298178111 11963370055576558947267167)
        ·
          refine ⟨17945055083364838420900751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963370055576558947267167 17945055083364838420900751)
          ·
            refine ⟨26917582625047257631351127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945055083364838420900751 26917582625047257631351127)
            ·
              refine ⟨40376373937570886447026691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26917582625047257631351127 40376373937570886447026691)
              ·
                refine ⟨60564560906356329670540037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40376373937570886447026691 60564560906356329670540037)
                ·
                  refine ⟨11355855169941811813226257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60564560906356329670540037 11355855169941811813226257)
                  ·
                    refine ⟨8516891377456358859919693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11355855169941811813226257 8516891377456358859919693)
                    ·
                      refine ⟨3193834266546134572469885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516891377456358859919693 3193834266546134572469885)
                      ·
                        rfl

theorem cell23_6219970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6219970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219970 prefixEnd_6219970 := by exact prefixLift 6219970
  have htrace : WordTrace (prefixWord ++ tailWord_6219970) baseStart_6219970 baseEnd_6219970 := by
    simpa [prefixWord, tailWord_6219970, baseEnd_6219970] using wordTrace_append hprefix tailTrace_6219970
  have hstable : (prefixWord ++ tailWord_6219970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219970).length < 2 ^ (prefixWord ++ tailWord_6219970).sum := by decide
  have hdescent : baseEnd_6219970 < baseStart_6219970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219990 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_6219990 : Nat := 118140960795 + 6219990 * 2 ^ 59
def prefixEnd_6219990 : Nat := 4983230072969 + 3 ^ 40 * 6219990 * 2
def baseEnd_6219990 : Nat := 354871615128802721579977

theorem tailTrace_6219990 : CollatzResearch.WordTrace tailWord_6219990 prefixEnd_6219990 354871615128802721579977 := by
  unfold tailWord_6219990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14178854546002874660244089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151241115157363996375936949 14178854546002874660244089)
  ·
    refine ⟨10634140909502155995183067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14178854546002874660244089 10634140909502155995183067)
    ·
      refine ⟨15951211364253233992774601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10634140909502155995183067 15951211364253233992774601)
      ·
        refine ⟨11963408523189925494580951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15951211364253233992774601 11963408523189925494580951)
        ·
          refine ⟨17945112784784888241871427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963408523189925494580951 17945112784784888241871427)
          ·
            refine ⟨26917669177177332362807141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945112784784888241871427 26917669177177332362807141)
            ·
              refine ⟨5047062970720749818026339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26917669177177332362807141 5047062970720749818026339)
              ·
                refine ⟨7570594456081124727039509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047062970720749818026339 7570594456081124727039509)
                ·
                  refine ⟨354871615128802721579977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7570594456081124727039509 354871615128802721579977)
                  ·
                    rfl

theorem cell23_6219990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_6219990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219990 prefixEnd_6219990 := by exact prefixLift 6219990
  have htrace : WordTrace (prefixWord ++ tailWord_6219990) baseStart_6219990 baseEnd_6219990 := by
    simpa [prefixWord, tailWord_6219990, baseEnd_6219990] using wordTrace_append hprefix tailTrace_6219990
  have hstable : (prefixWord ++ tailWord_6219990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219990).length < 2 ^ (prefixWord ++ tailWord_6219990).sum := by decide
  have hdescent : baseEnd_6219990 < baseStart_6219990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6219999 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 1, 6]
def baseStart_6219999 : Nat := 118140960795 + 6219999 * 2 ^ 59
def prefixEnd_6219999 : Nat := 4983230072969 + 3 ^ 40 * 6219999 * 2
def baseEnd_6219999 : Nat := 1064616385828371653002417

theorem tailTrace_6219999 : CollatzResearch.WordTrace tailWord_6219999 prefixEnd_6219999 1064616385828371653002417 := by
  unfold tailWord_6219999
  simp only [CollatzResearch.WordTrace]
  refine ⟨226862000993013389100983051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151241333995342259400655367 226862000993013389100983051)
  ·
    refine ⟨340293001489520083651474577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226862000993013389100983051 340293001489520083651474577)
    ·
      refine ⟨255219751117140062738605933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340293001489520083651474577 255219751117140062738605933)
      ·
        refine ⟨95707406668927523526977225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255219751117140062738605933 95707406668927523526977225)
        ·
          refine ⟨71780555001695642645232919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95707406668927523526977225 71780555001695642645232919)
          ·
            refine ⟨107670832502543463967849379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71780555001695642645232919 107670832502543463967849379)
            ·
              refine ⟨161506248753815195951774069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107670832502543463967849379 161506248753815195951774069)
              ·
                refine ⟨15141210820670174620478819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161506248753815195951774069 15141210820670174620478819)
                ·
                  refine ⟨22711816231005261930718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15141210820670174620478819 22711816231005261930718229)
                  ·
                    refine ⟨1064616385828371653002417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22711816231005261930718229 1064616385828371653002417)
                    ·
                      rfl

theorem cell23_6219999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_6219999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6219999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6219999 prefixEnd_6219999 := by exact prefixLift 6219999
  have htrace : WordTrace (prefixWord ++ tailWord_6219999) baseStart_6219999 baseEnd_6219999 := by
    simpa [prefixWord, tailWord_6219999, baseEnd_6219999] using wordTrace_append hprefix tailTrace_6219999
  have hstable : (prefixWord ++ tailWord_6219999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6219999).length < 2 ^ (prefixWord ++ tailWord_6219999).sum := by decide
  have hdescent : baseEnd_6219999 < baseStart_6219999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6219999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220003 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 3, 5]
def baseStart_6220003 : Nat := 118140960795 + 6220003 * 2 ^ 59
def prefixEnd_6220003 : Nat := 4983230072969 + 3 ^ 40 * 6220003 * 2
def baseEnd_6220003 : Nat := 1064617070469244314452411

theorem tailTrace_6220003 : CollatzResearch.WordTrace tailWord_6220003 prefixEnd_6220003 1064617070469244314452411 := by
  unfold tailWord_6220003
  simp only [CollatzResearch.WordTrace]
  refine ⟨226862146884998897784128663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151241431256665931856085775 226862146884998897784128663)
  ·
    refine ⟨340293220327498346676192995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226862146884998897784128663 340293220327498346676192995)
    ·
      refine ⟨510439830491247520014289493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340293220327498346676192995 510439830491247520014289493)
      ·
        refine ⟨5981716763569306875167455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 510439830491247520014289493 5981716763569306875167455)
        ·
          refine ⟨8972575145353960312751183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981716763569306875167455 8972575145353960312751183)
          ·
            refine ⟨13458862718030940469126775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972575145353960312751183 13458862718030940469126775)
            ·
              refine ⟨20188294077046410703690163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13458862718030940469126775 20188294077046410703690163)
              ·
                refine ⟨30282441115569616055535245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20188294077046410703690163 30282441115569616055535245)
                ·
                  refine ⟨11355915418338606020825717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30282441115569616055535245 11355915418338606020825717)
                  ·
                    refine ⟨1064617070469244314452411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11355915418338606020825717 1064617070469244314452411)
                    ·
                      rfl

theorem cell23_6220003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 5].length) (baseStart_6220003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220003 prefixEnd_6220003 := by exact prefixLift 6220003
  have htrace : WordTrace (prefixWord ++ tailWord_6220003) baseStart_6220003 baseEnd_6220003 := by
    simpa [prefixWord, tailWord_6220003, baseEnd_6220003] using wordTrace_append hprefix tailTrace_6220003
  have hstable : (prefixWord ++ tailWord_6220003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220003).length < 2 ^ (prefixWord ++ tailWord_6220003).sum := by decide
  have hdescent : baseEnd_6220003 < baseStart_6220003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220009 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_6220009 : Nat := 118140960795 + 6220009 * 2 ^ 59
def prefixEnd_6220009 : Nat := 4983230072969 + 3 ^ 40 * 6220009 * 2
def baseEnd_6220009 : Nat := 3193854292291659919882205

theorem tailTrace_6220009 : CollatzResearch.WordTrace tailWord_6220009 prefixEnd_6220009 3193854292291659919882205 := by
  unfold tailWord_6220009
  simp only [CollatzResearch.WordTrace]
  refine ⟨226862365722977160808847081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151241577148651440539231387 226862365722977160808847081)
  ·
    refine ⟨170146774292232870606635311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226862365722977160808847081 170146774292232870606635311)
    ·
      refine ⟨255220161438349305909952967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170146774292232870606635311 255220161438349305909952967)
      ·
        refine ⟨382830242157523958864929451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255220161438349305909952967 382830242157523958864929451)
        ·
          refine ⟨574245363236285938297394177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382830242157523958864929451 574245363236285938297394177)
          ·
            refine ⟨430684022427214453723045633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574245363236285938297394177 430684022427214453723045633)
            ·
              refine ⟨323013016820410840292284225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430684022427214453723045633 323013016820410840292284225)
              ·
                refine ⟨242259762615308130219213169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323013016820410840292284225 242259762615308130219213169)
                ·
                  refine ⟨181694821961481097664409877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242259762615308130219213169 181694821961481097664409877)
                  ·
                    refine ⟨8516944779444426453019213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181694821961481097664409877 8516944779444426453019213)
                    ·
                      refine ⟨3193854292291659919882205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516944779444426453019213 3193854292291659919882205)
                      ·
                        rfl

theorem cell23_6220009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_6220009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220009 prefixEnd_6220009 := by exact prefixLift 6220009
  have htrace : WordTrace (prefixWord ++ tailWord_6220009) baseStart_6220009 baseEnd_6220009 := by
    simpa [prefixWord, tailWord_6220009, baseEnd_6220009] using wordTrace_append hprefix tailTrace_6220009
  have hstable : (prefixWord ++ tailWord_6220009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220009).length < 2 ^ (prefixWord ++ tailWord_6220009).sum := by decide
  have hdescent : baseEnd_6220009 < baseStart_6220009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220026 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_6220026 : Nat := 118140960795 + 6220026 * 2 ^ 59
def prefixEnd_6220026 : Nat := 4983230072969 + 3 ^ 40 * 6220026 * 2
def baseEnd_6220026 : Nat := 3193863021462786353369627

theorem tailTrace_6220026 : CollatzResearch.WordTrace tailWord_6220026 prefixEnd_6220026 3193863021462786353369627 := by
  unfold tailWord_6220026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56715746440978893178053983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151241990509277048474810621 56715746440978893178053983)
  ·
    refine ⟨85073619661468339767080975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56715746440978893178053983 85073619661468339767080975)
    ·
      refine ⟨127610429492202509650621463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85073619661468339767080975 127610429492202509650621463)
      ·
        refine ⟨191415644238303764475932195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127610429492202509650621463 191415644238303764475932195)
        ·
          refine ⟨287123466357455646713898293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191415644238303764475932195 287123466357455646713898293)
          ·
            refine ⟨26917824971011466879427965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287123466357455646713898293 26917824971011466879427965)
            ·
              refine ⟨10094184364129300079785487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26917824971011466879427965 10094184364129300079785487)
              ·
                refine ⟨15141276546193950119678231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10094184364129300079785487 15141276546193950119678231)
                ·
                  refine ⟨22711914819290925179517347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15141276546193950119678231 22711914819290925179517347)
                  ·
                    refine ⟨34067872228936387769276021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22711914819290925179517347 34067872228936387769276021)
                    ·
                      refine ⟨3193863021462786353369627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34067872228936387769276021 3193863021462786353369627)
                      ·
                        rfl

theorem cell23_6220026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_6220026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220026 prefixEnd_6220026 := by exact prefixLift 6220026
  have htrace : WordTrace (prefixWord ++ tailWord_6220026) baseStart_6220026 baseEnd_6220026 := by
    simpa [prefixWord, tailWord_6220026, baseEnd_6220026] using wordTrace_append hprefix tailTrace_6220026
  have hstable : (prefixWord ++ tailWord_6220026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220026).length < 2 ^ (prefixWord ++ tailWord_6220026).sum := by decide
  have hdescent : baseEnd_6220026 < baseStart_6220026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220033 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_6220033 : Nat := 118140960795 + 6220033 * 2 ^ 59
def prefixEnd_6220033 : Nat := 4983230072969 + 3 ^ 40 * 6220033 * 2
def baseEnd_6220033 : Nat := 1064622205275789275327365

theorem tailTrace_6220033 : CollatzResearch.WordTrace tailWord_6220033 prefixEnd_6220033 1064622205275789275327365 := by
  unfold tailWord_6220033
  simp only [CollatzResearch.WordTrace]
  refine ⟨226863241074890212907720753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151242160716593475271813835 226863241074890212907720753)
  ·
    refine ⟨170147430806167659680790565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226863241074890212907720753 170147430806167659680790565)
    ·
      refine ⟨31902643276156436190148231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170147430806167659680790565 31902643276156436190148231)
      ·
        refine ⟨47853964914234654285222347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31902643276156436190148231 47853964914234654285222347)
        ·
          refine ⟨71780947371351981427833521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47853964914234654285222347 71780947371351981427833521)
          ·
            refine ⟨53835710528513986070875141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71780947371351981427833521 53835710528513986070875141)
            ·
              refine ⟨10094195724096372388289089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53835710528513986070875141 10094195724096372388289089)
              ·
                refine ⟨7570646793072279291216817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10094195724096372388289089 7570646793072279291216817)
                ·
                  refine ⟨5677985094804209468412613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7570646793072279291216817 5677985094804209468412613)
                  ·
                    refine ⟨1064622205275789275327365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5677985094804209468412613 1064622205275789275327365)
                    ·
                      rfl

theorem cell23_6220033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_6220033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220033 prefixEnd_6220033 := by exact prefixLift 6220033
  have htrace : WordTrace (prefixWord ++ tailWord_6220033) baseStart_6220033 baseEnd_6220033 := by
    simpa [prefixWord, tailWord_6220033, baseEnd_6220033] using wordTrace_append hprefix tailTrace_6220033
  have hstable : (prefixWord ++ tailWord_6220033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220033).length < 2 ^ (prefixWord ++ tailWord_6220033).sum := by decide
  have hdescent : baseEnd_6220033 < baseStart_6220033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220034 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6220034 : Nat := 118140960795 + 6220034 * 2 ^ 59
def prefixEnd_6220034 : Nat := 4983230072969 + 3 ^ 40 * 6220034 * 2
def baseEnd_6220034 : Nat := 3193867129308022322069591

theorem tailTrace_6220034 : CollatzResearch.WordTrace tailWord_6220034 prefixEnd_6220034 3193867129308022322069591 := by
  unfold tailWord_6220034
  simp only [CollatzResearch.WordTrace]
  refine ⟨56715819386971647519626789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151242185031924393385671437 56715819386971647519626789)
  ·
    refine ⟨10634216135057183909930023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56715819386971647519626789 10634216135057183909930023)
    ·
      refine ⟨15951324202585775864895035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10634216135057183909930023 15951324202585775864895035)
      ·
        refine ⟨23926986303878663797342553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15951324202585775864895035 23926986303878663797342553)
        ·
          refine ⟨17945239727908997848006915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23926986303878663797342553 17945239727908997848006915)
          ·
            refine ⟨26917859591863496772010373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945239727908997848006915 26917859591863496772010373)
            ·
              refine ⟨5047098673474405644751945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26917859591863496772010373 5047098673474405644751945)
              ·
                refine ⟨3785324005105804233563959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5047098673474405644751945 3785324005105804233563959)
                ·
                  refine ⟨5677986007658706350345939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785324005105804233563959 5677986007658706350345939)
                  ·
                    refine ⟨8516979011488059525518909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5677986007658706350345939 8516979011488059525518909)
                    ·
                      refine ⟨3193867129308022322069591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8516979011488059525518909 3193867129308022322069591)
                      ·
                        rfl

theorem cell23_6220034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6220034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220034 prefixEnd_6220034 := by exact prefixLift 6220034
  have htrace : WordTrace (prefixWord ++ tailWord_6220034) baseStart_6220034 baseEnd_6220034 := by
    simpa [prefixWord, tailWord_6220034, baseEnd_6220034] using wordTrace_append hprefix tailTrace_6220034
  have hstable : (prefixWord ++ tailWord_6220034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220034).length < 2 ^ (prefixWord ++ tailWord_6220034).sum := by decide
  have hdescent : baseEnd_6220034 < baseStart_6220034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220071 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6220071 : Nat := 118140960795 + 6220071 * 2 ^ 59
def prefixEnd_6220071 : Nat := 4983230072969 + 3 ^ 40 * 6220071 * 2
def baseEnd_6220071 : Nat := 1064628709364079559102307

theorem tailTrace_6220071 : CollatzResearch.WordTrace tailWord_6220071 prefixEnd_6220071 1064628709364079559102307 := by
  unfold tailWord_6220071
  simp only [CollatzResearch.WordTrace]
  refine ⟨226864627048752545397604067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151243084699168363598402711 226864627048752545397604067)
  ·
    refine ⟨340296940573128818096406101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226864627048752545397604067 340296940573128818096406101)
    ·
      refine ⟨3987854772341353337067259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 340296940573128818096406101 3987854772341353337067259)
      ·
        refine ⟨5981782158512030005600889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987854772341353337067259 5981782158512030005600889)
        ·
          refine ⟨4486336618884022504200667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5981782158512030005600889 4486336618884022504200667)
          ·
            refine ⟨6729504928326033756301001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486336618884022504200667 6729504928326033756301001)
            ·
              refine ⟨5047128696244525317225751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6729504928326033756301001 5047128696244525317225751)
              ·
                refine ⟨7570693044366787975838627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047128696244525317225751 7570693044366787975838627)
                ·
                  refine ⟨11356039566550181963757941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570693044366787975838627 11356039566550181963757941)
                  ·
                    refine ⟨1064628709364079559102307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11356039566550181963757941 1064628709364079559102307)
                    ·
                      rfl

theorem cell23_6220071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6220071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220071 prefixEnd_6220071 := by exact prefixLift 6220071
  have htrace : WordTrace (prefixWord ++ tailWord_6220071) baseStart_6220071 baseEnd_6220071 := by
    simpa [prefixWord, tailWord_6220071, baseEnd_6220071] using wordTrace_append hprefix tailTrace_6220071
  have hstable : (prefixWord ++ tailWord_6220071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220071).length < 2 ^ (prefixWord ++ tailWord_6220071).sum := by decide
  have hdescent : baseEnd_6220071 < baseStart_6220071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220074 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6220074 : Nat := 118140960795 + 6220074 * 2 ^ 59
def prefixEnd_6220074 : Nat := 4983230072969 + 3 ^ 40 * 6220074 * 2
def baseEnd_6220074 : Nat := 3193887668534202165569407

theorem tailTrace_6220074 : CollatzResearch.WordTrace tailWord_6220074 prefixEnd_6220074 3193887668534202165569407 := by
  unfold tailWord_6220074
  simp only [CollatzResearch.WordTrace]
  refine ⟨56716184116935419227490819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151243157645161117939975517 56716184116935419227490819)
  ·
    refine ⟨85074276175403128841236229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56716184116935419227490819 85074276175403128841236229)
    ·
      refine ⟨15951426782888086657731793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85074276175403128841236229 15951426782888086657731793)
      ·
        refine ⟨11963570087166064993298845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15951426782888086657731793 11963570087166064993298845)
        ·
          refine ⟨4486338782687274372487067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11963570087166064993298845 4486338782687274372487067)
          ·
            refine ⟨6729508174030911558730601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486338782687274372487067 6729508174030911558730601)
            ·
              refine ⟨5047131130523183669047951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6729508174030911558730601 5047131130523183669047951)
              ·
                refine ⟨7570696695784775503571927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047131130523183669047951 7570696695784775503571927)
                ·
                  refine ⟨11356045043677163255357891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570696695784775503571927 11356045043677163255357891)
                  ·
                    refine ⟨17034067565515744883036837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11356045043677163255357891 17034067565515744883036837)
                    ·
                      refine ⟨3193887668534202165569407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17034067565515744883036837 3193887668534202165569407)
                      ·
                        rfl

theorem cell23_6220074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6220074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220074 prefixEnd_6220074 := by exact prefixLift 6220074
  have htrace : WordTrace (prefixWord ++ tailWord_6220074) baseStart_6220074 baseEnd_6220074 := by
    simpa [prefixWord, tailWord_6220074, baseEnd_6220074] using wordTrace_append hprefix tailTrace_6220074
  have hstable : (prefixWord ++ tailWord_6220074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220074).length < 2 ^ (prefixWord ++ tailWord_6220074).sum := by decide
  have hdescent : baseEnd_6220074 < baseStart_6220074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220077 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6220077 : Nat := 118140960795 + 6220077 * 2 ^ 59
def prefixEnd_6220077 : Nat := 4983230072969 + 3 ^ 40 * 6220077 * 2
def baseEnd_6220077 : Nat := 3193889208976165653831893

theorem tailTrace_6220077 : CollatzResearch.WordTrace tailWord_6220077 prefixEnd_6220077 3193889208976165653831893 := by
  unfold tailWord_6220077
  simp only [CollatzResearch.WordTrace]
  refine ⟨226864845886730808422322485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151243230591153872281548323 226864845886730808422322485)
  ·
    refine ⟨21268579301881013289592733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226864845886730808422322485 21268579301881013289592733)
    ·
      refine ⟨7975717238205379983597275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21268579301881013289592733 7975717238205379983597275)
      ·
        refine ⟨11963575857308069975395913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975717238205379983597275 11963575857308069975395913)
        ·
          refine ⟨8972681892981052481546935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11963575857308069975395913 8972681892981052481546935)
          ·
            refine ⟨13459022839471578722320403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972681892981052481546935 13459022839471578722320403)
            ·
              refine ⟨20188534259207368083480605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13459022839471578722320403 20188534259207368083480605)
              ·
                refine ⟨7570700347202763031305227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20188534259207368083480605 7570700347202763031305227)
                ·
                  refine ⟨11356050520804144546957841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570700347202763031305227 11356050520804144546957841)
                  ·
                    refine ⟨8517037890603108410218381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11356050520804144546957841 8517037890603108410218381)
                    ·
                      refine ⟨3193889208976165653831893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517037890603108410218381 3193889208976165653831893)
                      ·
                        rfl

theorem cell23_6220077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6220077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220077 prefixEnd_6220077 := by exact prefixLift 6220077
  have htrace : WordTrace (prefixWord ++ tailWord_6220077) baseStart_6220077 baseEnd_6220077 := by
    simpa [prefixWord, tailWord_6220077, baseEnd_6220077] using wordTrace_append hprefix tailTrace_6220077
  have hstable : (prefixWord ++ tailWord_6220077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220077).length < 2 ^ (prefixWord ++ tailWord_6220077).sum := by decide
  have hdescent : baseEnd_6220077 < baseStart_6220077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220090 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_6220090 : Nat := 118140960795 + 6220090 * 2 ^ 59
def prefixEnd_6220090 : Nat := 4983230072969 + 3 ^ 40 * 6220090 * 2
def baseEnd_6220090 : Nat := 3193895884224674102969333

theorem tailTrace_6220090 : CollatzResearch.WordTrace tailWord_6220090 prefixEnd_6220090 3193895884224674102969333 := by
  unfold tailWord_6220090
  simp only [CollatzResearch.WordTrace]
  refine ⟨56716330008920927910636431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151243546690455807761697149 56716330008920927910636431)
  ·
    refine ⟨85074495013381391865954647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56716330008920927910636431 85074495013381391865954647)
    ·
      refine ⟨127611742520072087798931971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85074495013381391865954647 127611742520072087798931971)
      ·
        refine ⟨191417613780108131698397957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127611742520072087798931971 191417613780108131698397957)
        ·
          refine ⟨35890802583770274693449617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191417613780108131698397957 35890802583770274693449617)
          ·
            refine ⟨26918101937827706020087213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35890802583770274693449617 26918101937827706020087213)
            ·
              refine ⟨10094288226685389757532705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26918101937827706020087213 10094288226685389757532705)
              ·
                refine ⟨7570716170014042318149529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10094288226685389757532705 7570716170014042318149529)
                ·
                  refine ⟨5678037127510531738612147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7570716170014042318149529 5678037127510531738612147)
                  ·
                    refine ⟨8517055691265797607918221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5678037127510531738612147 8517055691265797607918221)
                    ·
                      refine ⟨3193895884224674102969333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517055691265797607918221 3193895884224674102969333)
                      ·
                        rfl

theorem cell23_6220090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_6220090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220090 prefixEnd_6220090 := by exact prefixLift 6220090
  have htrace : WordTrace (prefixWord ++ tailWord_6220090) baseStart_6220090 baseEnd_6220090 := by
    simpa [prefixWord, tailWord_6220090, baseEnd_6220090] using wordTrace_append hprefix tailTrace_6220090
  have hstable : (prefixWord ++ tailWord_6220090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220090).length < 2 ^ (prefixWord ++ tailWord_6220090).sum := by decide
  have hdescent : baseEnd_6220090 < baseStart_6220090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220117 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6220117 : Nat := 118140960795 + 6220117 * 2 ^ 59
def prefixEnd_6220117 : Nat := 4983230072969 + 3 ^ 40 * 6220117 * 2
def baseEnd_6220117 : Nat := 3193909748202345497331709

theorem tailTrace_6220117 : CollatzResearch.WordTrace tailWord_6220117 prefixEnd_6220117 3193909748202345497331709 := by
  unfold tailWord_6220117
  simp only [CollatzResearch.WordTrace]
  refine ⟨226866304806585895253778605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151244203204390596835852403 226866304806585895253778605)
  ·
    refine ⟨85074864302469710720166977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226866304806585895253778605 85074864302469710720166977)
    ·
      refine ⟨63806148226852283040125233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85074864302469710720166977 63806148226852283040125233)
      ·
        refine ⟨47854611170139212280093925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63806148226852283040125233 47854611170139212280093925)
        ·
          refine ⟨8972739594401102302517611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47854611170139212280093925 8972739594401102302517611)
          ·
            refine ⟨13459109391601653453776417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8972739594401102302517611 13459109391601653453776417)
            ·
              refine ⟨10094332043701240090332313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13459109391601653453776417 10094332043701240090332313)
              ·
                refine ⟨7570749032775930067749235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10094332043701240090332313 7570749032775930067749235)
                ·
                  refine ⟨11356123549163895101623853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7570749032775930067749235 11356123549163895101623853)
                  ·
                    refine ⟨4258546330936460663108945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11356123549163895101623853 4258546330936460663108945)
                    ·
                      refine ⟨3193909748202345497331709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258546330936460663108945 3193909748202345497331709)
                      ·
                        rfl

theorem cell23_6220117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6220117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220117 prefixEnd_6220117 := by exact prefixLift 6220117
  have htrace : WordTrace (prefixWord ++ tailWord_6220117) baseStart_6220117 baseEnd_6220117 := by
    simpa [prefixWord, tailWord_6220117, baseEnd_6220117] using wordTrace_append hprefix tailTrace_6220117
  have hstable : (prefixWord ++ tailWord_6220117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220117).length < 2 ^ (prefixWord ++ tailWord_6220117).sum := by decide
  have hdescent : baseEnd_6220117 < baseStart_6220117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220200 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6220200 : Nat := 118140960795 + 6220200 * 2 ^ 59
def prefixEnd_6220200 : Nat := 4983230072969 + 3 ^ 40 * 6220200 * 2
def baseEnd_6220200 : Nat := 1064650789032222890864609

theorem tailTrace_6220200 : CollatzResearch.WordTrace tailWord_6220200 prefixEnd_6220200 1064650789032222890864609 := by
  unfold tailWord_6220200
  simp only [CollatzResearch.WordTrace]
  refine ⟨113434666032642600214525027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151246221376856800286033369 113434666032642600214525027)
  ·
    refine ⟨170151999048963900321787541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113434666032642600214525027 170151999048963900321787541)
    ·
      refine ⟨7975874955420182827583791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170151999048963900321787541 7975874955420182827583791)
      ·
        refine ⟨11963812433130274241375687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7975874955420182827583791 11963812433130274241375687)
        ·
          refine ⟨17945718649695411362063531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963812433130274241375687 17945718649695411362063531)
          ·
            refine ⟨26918577974543117043095297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945718649695411362063531 26918577974543117043095297)
            ·
              refine ⟨20188933480907337782321473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26918577974543117043095297 20188933480907337782321473)
              ·
                refine ⟨15141700110680503336741105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20188933480907337782321473 15141700110680503336741105)
                ·
                  refine ⟨11356275083010377502555829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15141700110680503336741105 11356275083010377502555829)
                  ·
                    refine ⟨1064650789032222890864609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11356275083010377502555829 1064650789032222890864609)
                    ·
                      rfl

theorem cell23_6220200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6220200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220200 prefixEnd_6220200 := by exact prefixLift 6220200
  have htrace : WordTrace (prefixWord ++ tailWord_6220200) baseStart_6220200 baseEnd_6220200 := by
    simpa [prefixWord, tailWord_6220200, baseEnd_6220200] using wordTrace_append hprefix tailTrace_6220200
  have hstable : (prefixWord ++ tailWord_6220200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220200).length < 2 ^ (prefixWord ++ tailWord_6220200).sum := by decide
  have hdescent : baseEnd_6220200 < baseStart_6220200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220216 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_6220216 : Nat := 118140960795 + 6220216 * 2 ^ 59
def prefixEnd_6220216 : Nat := 4983230072969 + 3 ^ 40 * 6220216 * 2
def baseEnd_6220216 : Nat := 3193960582787140609993753

theorem tailTrace_6220216 : CollatzResearch.WordTrace tailWord_6220216 prefixEnd_6220216 3193960582787140609993753 := by
  unfold tailWord_6220216
  simp only [CollatzResearch.WordTrace]
  refine ⟨113434957816613617580816251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151246610422151490107755001 113434957816613617580816251)
  ·
    refine ⟨170152436724920426371224377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113434957816613617580816251 170152436724920426371224377)
    ·
      refine ⟨127614327543690319778418283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170152436724920426371224377 127614327543690319778418283)
      ·
        refine ⟨191421491315535479667627425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127614327543690319778418283 191421491315535479667627425)
        ·
          refine ⟨143566118486651609750720569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191421491315535479667627425 143566118486651609750720569)
          ·
            refine ⟨107674588864988707313040427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143566118486651609750720569 107674588864988707313040427)
            ·
              refine ⟨161511883297483060969560641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107674588864988707313040427 161511883297483060969560641)
              ·
                refine ⟨121133912473112295727170481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161511883297483060969560641 121133912473112295727170481)
                ·
                  refine ⟨90850434354834221795377861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121133912473112295727170481 90850434354834221795377861)
                  ·
                    refine ⟨17034456441531416586633349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90850434354834221795377861 17034456441531416586633349)
                    ·
                      refine ⟨3193960582787140609993753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17034456441531416586633349 3193960582787140609993753)
                      ·
                        rfl

theorem cell23_6220216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_6220216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220216 prefixEnd_6220216 := by exact prefixLift 6220216
  have htrace : WordTrace (prefixWord ++ tailWord_6220216) baseStart_6220216 baseEnd_6220216 := by
    simpa [prefixWord, tailWord_6220216, baseEnd_6220216] using wordTrace_append hprefix tailTrace_6220216
  have hstable : (prefixWord ++ tailWord_6220216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220216).length < 2 ^ (prefixWord ++ tailWord_6220216).sum := by decide
  have hdescent : baseEnd_6220216 < baseStart_6220216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220220 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6220220 : Nat := 118140960795 + 6220220 * 2 ^ 59
def prefixEnd_6220220 : Nat := 4983230072969 + 3 ^ 40 * 6220220 * 2
def baseEnd_6220220 : Nat := 3193962636709758594343735

theorem tailTrace_6220220 : CollatzResearch.WordTrace tailWord_6220220 prefixEnd_6220220 3193962636709758594343735 := by
  unfold tailWord_6220220
  simp only [CollatzResearch.WordTrace]
  refine ⟨113435030762606371922389057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151246707683475162563185409 113435030762606371922389057)
  ·
    refine ⟨85076273071954778941791793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113435030762606371922389057 85076273071954778941791793)
    ·
      refine ⟨63807204803966084206343845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85076273071954778941791793 63807204803966084206343845)
      ·
        refine ⟨11963850900743640788689471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63807204803966084206343845 11963850900743640788689471)
        ·
          refine ⟨17945776351115461183034207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11963850900743640788689471 17945776351115461183034207)
          ·
            refine ⟨26918664526673191774551311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17945776351115461183034207 26918664526673191774551311)
            ·
              refine ⟨40377996790009787661826967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26918664526673191774551311 40377996790009787661826967)
              ·
                refine ⟨60566995185014681492740451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40377996790009787661826967 60566995185014681492740451)
                ·
                  refine ⟨90850492777522022239110677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60566995185014681492740451 90850492777522022239110677)
                  ·
                    refine ⟨4258616848946344792458313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90850492777522022239110677 4258616848946344792458313)
                    ·
                      refine ⟨3193962636709758594343735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258616848946344792458313 3193962636709758594343735)
                      ·
                        rfl

theorem cell23_6220220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6220220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220220 prefixEnd_6220220 := by exact prefixLift 6220220
  have htrace : WordTrace (prefixWord ++ tailWord_6220220) baseStart_6220220 baseEnd_6220220 := by
    simpa [prefixWord, tailWord_6220220, baseEnd_6220220] using wordTrace_append hprefix tailTrace_6220220
  have hstable : (prefixWord ++ tailWord_6220220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220220).length < 2 ^ (prefixWord ++ tailWord_6220220).sum := by decide
  have hdescent : baseEnd_6220220 < baseStart_6220220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220293 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_6220293 : Nat := 118140960795 + 6220293 * 2 ^ 59
def prefixEnd_6220293 : Nat := 4983230072969 + 3 ^ 40 * 6220293 * 2
def baseEnd_6220293 : Nat := 3194000120797536808730899

theorem tailTrace_6220293 : CollatzResearch.WordTrace tailWord_6220293 prefixEnd_6220293 3194000120797536808730899 := by
  unfold tailWord_6220293
  simp only [CollatzResearch.WordTrace]
  refine ⟨226872724053948277312185533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151248482702632184874790355 226872724053948277312185533)
  ·
    refine ⟨85077271520230603992069575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226872724053948277312185533 85077271520230603992069575)
    ·
      refine ⟨127615907280345905988104363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85077271520230603992069575 127615907280345905988104363)
      ·
        refine ⟨191423860920518858982156545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127615907280345905988104363 191423860920518858982156545)
        ·
          refine ⟨143567895690389144236617409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191423860920518858982156545 143567895690389144236617409)
          ·
            refine ⟨107675921767791858177463057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143567895690389144236617409 107675921767791858177463057)
            ·
              refine ⟨80756941325843893633097293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107675921767791858177463057 80756941325843893633097293)
              ·
                refine ⟨30283852997191460112411485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80756941325843893633097293 30283852997191460112411485)
                ·
                  refine ⟨11356444873946797542154307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30283852997191460112411485 11356444873946797542154307)
                  ·
                    refine ⟨17034667310920196313231461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11356444873946797542154307 17034667310920196313231461)
                    ·
                      refine ⟨3194000120797536808730899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17034667310920196313231461 3194000120797536808730899)
                      ·
                        rfl

theorem cell23_6220293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_6220293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220293 prefixEnd_6220293 := by exact prefixLift 6220293
  have htrace : WordTrace (prefixWord ++ tailWord_6220293) baseStart_6220293 baseEnd_6220293 := by
    simpa [prefixWord, tailWord_6220293, baseEnd_6220293] using wordTrace_append hprefix tailTrace_6220293
  have hstable : (prefixWord ++ tailWord_6220293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220293).length < 2 ^ (prefixWord ++ tailWord_6220293).sum := by decide
  have hdescent : baseEnd_6220293 < baseStart_6220293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220303 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 4, 4]
def baseStart_6220303 : Nat := 118140960795 + 6220303 * 2 ^ 59
def prefixEnd_6220303 : Nat := 4983230072969 + 3 ^ 40 * 6220303 * 2
def baseEnd_6220303 : Nat := 1064668418534693923201951

theorem tailTrace_6220303 : CollatzResearch.WordTrace tailWord_6220303 prefixEnd_6220303 1064668418534693923201951 := by
  unfold tailWord_6220303
  simp only [CollatzResearch.WordTrace]
  refine ⟨226873088783912049020049563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151248725855941366013366375 226873088783912049020049563)
  ·
    refine ⟨340309633175868073530074345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226873088783912049020049563 340309633175868073530074345)
    ·
      refine ⟨255232224881901055147555759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340309633175868073530074345 255232224881901055147555759)
      ·
        refine ⟨382848337322851582721333639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255232224881901055147555759 382848337322851582721333639)
        ·
          refine ⟨574272505984277374082000459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382848337322851582721333639 574272505984277374082000459)
          ·
            refine ⟨861408758976416061123000689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574272505984277374082000459 861408758976416061123000689)
            ·
              refine ⟨646056569232312045842250517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861408758976416061123000689 646056569232312045842250517)
              ·
                refine ⟨30283901682764627148855493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 646056569232312045842250517 30283901682764627148855493)
                ·
                  refine ⟨5678231565518367590410405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30283901682764627148855493 5678231565518367590410405)
                  ·
                    refine ⟨1064668418534693923201951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678231565518367590410405 1064668418534693923201951)
                    ·
                      rfl

theorem cell23_6220303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_6220303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220303 prefixEnd_6220303 := by exact prefixLift 6220303
  have htrace : WordTrace (prefixWord ++ tailWord_6220303) baseStart_6220303 baseEnd_6220303 := by
    simpa [prefixWord, tailWord_6220303, baseEnd_6220303] using wordTrace_append hprefix tailTrace_6220303
  have hstable : (prefixWord ++ tailWord_6220303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220303).length < 2 ^ (prefixWord ++ tailWord_6220303).sum := by decide
  have hdescent : baseEnd_6220303 < baseStart_6220303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220323 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_6220323 : Nat := 118140960795 + 6220323 * 2 ^ 59
def prefixEnd_6220323 : Nat := 4983230072969 + 3 ^ 40 * 6220323 * 2
def baseEnd_6220323 : Nat := 3194015525217171691355761

theorem tailTrace_6220323 : CollatzResearch.WordTrace tailWord_6220323 prefixEnd_6220323 3194015525217171691355761 := by
  unfold tailWord_6220323
  simp only [CollatzResearch.WordTrace]
  refine ⟨226873818243839592435777623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151249212162559728290518415 226873818243839592435777623)
  ·
    refine ⟨340310727365759388653666435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226873818243839592435777623 340310727365759388653666435)
    ·
      refine ⟨510466091048639082980499653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340310727365759388653666435 510466091048639082980499653)
      ·
        refine ⟨95712392071619828058843685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 510466091048639082980499653 95712392071619828058843685)
        ·
          refine ⟨17946073513428717761033191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95712392071619828058843685 17946073513428717761033191)
          ·
            refine ⟨26919110270143076641549787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17946073513428717761033191 26919110270143076641549787)
            ·
              refine ⟨40378665405214614962324681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26919110270143076641549787 40378665405214614962324681)
              ·
                refine ⟨30283999053910961221743511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40378665405214614962324681 30283999053910961221743511)
                ·
                  refine ⟨45425998580866441832615267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30283999053910961221743511 45425998580866441832615267)
                  ·
                    refine ⟨68138997871299662748922901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45425998580866441832615267 68138997871299662748922901)
                    ·
                      refine ⟨3194015525217171691355761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68138997871299662748922901 3194015525217171691355761)
                      ·
                        rfl

theorem cell23_6220323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_6220323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220323 prefixEnd_6220323 := by exact prefixLift 6220323
  have htrace : WordTrace (prefixWord ++ tailWord_6220323) baseStart_6220323 baseEnd_6220323 := by
    simpa [prefixWord, tailWord_6220323, baseEnd_6220323] using wordTrace_append hprefix tailTrace_6220323
  have hstable : (prefixWord ++ tailWord_6220323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220323).length < 2 ^ (prefixWord ++ tailWord_6220323).sum := by decide
  have hdescent : baseEnd_6220323 < baseStart_6220323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220330 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6220330 : Nat := 118140960795 + 6220330 * 2 ^ 59
def prefixEnd_6220330 : Nat := 4983230072969 + 3 ^ 40 * 6220330 * 2
def baseEnd_6220330 : Nat := 3194019119581753163968229

theorem tailTrace_6220330 : CollatzResearch.WordTrace tailWord_6220330 prefixEnd_6220330 3194019119581753163968229 := by
  unfold tailWord_6220330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56718518388703558157820611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151249382369876155087521629 56718518388703558157820611)
  ·
    refine ⟨85077777583055337236730917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56718518388703558157820611 85077777583055337236730917)
    ·
      refine ⟨15952083296822875731887047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85077777583055337236730917 15952083296822875731887047)
      ·
        refine ⟨23928124945234313597830571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15952083296822875731887047 23928124945234313597830571)
        ·
          refine ⟨35892187417851470396745857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23928124945234313597830571 35892187417851470396745857)
          ·
            refine ⟨26919140563388602797559393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35892187417851470396745857 26919140563388602797559393)
            ·
              refine ⟨20189355422541452098169545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26919140563388602797559393 20189355422541452098169545)
              ·
                refine ⟨15142016566906089073627159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20189355422541452098169545 15142016566906089073627159)
                ·
                  refine ⟨22713024850359133610440739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15142016566906089073627159 22713024850359133610440739)
                  ·
                    refine ⟨34069537275538700415661109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22713024850359133610440739 34069537275538700415661109)
                    ·
                      refine ⟨3194019119581753163968229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34069537275538700415661109 3194019119581753163968229)
                      ·
                        rfl

theorem cell23_6220330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6220330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220330 prefixEnd_6220330 := by exact prefixLift 6220330
  have htrace : WordTrace (prefixWord ++ tailWord_6220330) baseStart_6220330 baseEnd_6220330 := by
    simpa [prefixWord, tailWord_6220330, baseEnd_6220330] using wordTrace_append hprefix tailTrace_6220330
  have hstable : (prefixWord ++ tailWord_6220330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220330).length < 2 ^ (prefixWord ++ tailWord_6220330).sum := by decide
  have hdescent : baseEnd_6220330 < baseStart_6220330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220337 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 2, 4]
def baseStart_6220337 : Nat := 118140960795 + 6220337 * 2 ^ 59
def prefixEnd_6220337 : Nat := 4983230072969 + 3 ^ 40 * 6220337 * 2
def baseEnd_6220337 : Nat := 1064674237982111545526899

theorem tailTrace_6220337 : CollatzResearch.WordTrace tailWord_6220337 prefixEnd_6220337 1064674237982111545526899 := by
  unfold tailWord_6220337
  simp only [CollatzResearch.WordTrace]
  refine ⟨226874328865788872826787265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151249552577192581884524843 226874328865788872826787265)
  ·
    refine ⟨170155746649341654620090449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226874328865788872826787265 170155746649341654620090449)
    ·
      refine ⟨127616809987006240965067837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170155746649341654620090449 127616809987006240965067837)
      ·
        refine ⟨47856303745127340361900439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127616809987006240965067837 47856303745127340361900439)
        ·
          refine ⟨71784455617691010542850659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47856303745127340361900439 71784455617691010542850659)
          ·
            refine ⟨107676683426536515814275989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71784455617691010542850659 107676683426536515814275989)
            ·
              refine ⟨5047344535618899178794187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107676683426536515814275989 5047344535618899178794187)
              ·
                refine ⟨7571016803428348768191281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047344535618899178794187 7571016803428348768191281)
                ·
                  refine ⟨5678262602571261576143461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7571016803428348768191281 5678262602571261576143461)
                  ·
                    refine ⟨1064674237982111545526899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678262602571261576143461 1064674237982111545526899)
                    ·
                      rfl

theorem cell23_6220337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_6220337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220337 prefixEnd_6220337 := by exact prefixLift 6220337
  have htrace : WordTrace (prefixWord ++ tailWord_6220337) baseStart_6220337 baseEnd_6220337 := by
    simpa [prefixWord, tailWord_6220337, baseEnd_6220337] using wordTrace_append hprefix tailTrace_6220337
  have hstable : (prefixWord ++ tailWord_6220337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220337).length < 2 ^ (prefixWord ++ tailWord_6220337).sum := by decide
  have hdescent : baseEnd_6220337 < baseStart_6220337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220360 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_6220360 : Nat := 118140960795 + 6220360 * 2 ^ 59
def prefixEnd_6220360 : Nat := 4983230072969 + 3 ^ 40 * 6220360 * 2
def baseEnd_6220360 : Nat := 3194034524001388046593091

theorem tailTrace_6220360 : CollatzResearch.WordTrace tailWord_6220360 prefixEnd_6220360 3194034524001388046593091 := by
  unfold tailWord_6220360
  simp only [CollatzResearch.WordTrace]
  refine ⟨113437583872352773877437267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151250111829803698503249689 113437583872352773877437267)
  ·
    refine ⟨170156375808529160816155901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113437583872352773877437267 170156375808529160816155901)
    ·
      refine ⟨63808640928198435306058463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170156375808529160816155901 63808640928198435306058463)
      ·
        refine ⟨95712961392297652959087695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63808640928198435306058463 95712961392297652959087695)
        ·
          refine ⟨143569442088446479438631543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95712961392297652959087695 143569442088446479438631543)
          ·
            refine ⟨215354163132669719157947315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143569442088446479438631543 215354163132669719157947315)
            ·
              refine ⟨323031244699004578736920973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215354163132669719157947315 323031244699004578736920973)
              ·
                refine ⟨121136716762126717026345365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323031244699004578736920973 121136716762126717026345365)
                ·
                  refine ⟨5678283598224689860609939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121136716762126717026345365 5678283598224689860609939)
                  ·
                    refine ⟨8517425397337034790914909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5678283598224689860609939 8517425397337034790914909)
                    ·
                      refine ⟨3194034524001388046593091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517425397337034790914909 3194034524001388046593091)
                      ·
                        rfl

theorem cell23_6220360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_6220360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220360 prefixEnd_6220360 := by exact prefixLift 6220360
  have htrace : WordTrace (prefixWord ++ tailWord_6220360) baseStart_6220360 baseEnd_6220360 := by
    simpa [prefixWord, tailWord_6220360, baseEnd_6220360] using wordTrace_append hprefix tailTrace_6220360
  have hstable : (prefixWord ++ tailWord_6220360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220360).length < 2 ^ (prefixWord ++ tailWord_6220360).sum := by decide
  have hdescent : baseEnd_6220360 < baseStart_6220360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220373 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6220373 : Nat := 118140960795 + 6220373 * 2 ^ 59
def prefixEnd_6220373 : Nat := 4983230072969 + 3 ^ 40 * 6220373 * 2
def baseEnd_6220373 : Nat := 3194041199249896495730531

theorem tailTrace_6220373 : CollatzResearch.WordTrace tailWord_6220373 prefixEnd_6220373 3194041199249896495730531 := by
  unfold tailWord_6220373
  simp only [CollatzResearch.WordTrace]
  refine ⟨226875641893658450975097773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151250427929105633983398515 226875641893658450975097773)
  ·
    refine ⟨85078365710121919115661665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226875641893658450975097773 85078365710121919115661665)
    ·
      refine ⟨63808774282591439336746249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85078365710121919115661665 63808774282591439336746249)
      ·
        refine ⟨47856580711943579502559687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63808774282591439336746249 47856580711943579502559687)
        ·
          refine ⟨71784871067915369253839531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47856580711943579502559687 71784871067915369253839531)
          ·
            refine ⟨107677306601873053880759297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71784871067915369253839531 107677306601873053880759297)
            ·
              refine ⟨80757979951404790410569473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107677306601873053880759297 80757979951404790410569473)
              ·
                refine ⟨60568484963553592807927105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80757979951404790410569473 60568484963553592807927105)
                ·
                  refine ⟨45426363722665194605945329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60568484963553592807927105 45426363722665194605945329)
                  ·
                    refine ⟨34069772791998895954458997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45426363722665194605945329 34069772791998895954458997)
                    ·
                      refine ⟨3194041199249896495730531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34069772791998895954458997 3194041199249896495730531)
                      ·
                        rfl

theorem cell23_6220373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6220373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220373 prefixEnd_6220373 := by exact prefixLift 6220373
  have htrace : WordTrace (prefixWord ++ tailWord_6220373) baseStart_6220373 baseEnd_6220373 := by
    simpa [prefixWord, tailWord_6220373, baseEnd_6220373] using wordTrace_append hprefix tailTrace_6220373
  have hstable : (prefixWord ++ tailWord_6220373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220373).length < 2 ^ (prefixWord ++ tailWord_6220373).sum := by decide
  have hdescent : baseEnd_6220373 < baseStart_6220373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220403 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_6220403 : Nat := 118140960795 + 6220403 * 2 ^ 59
def prefixEnd_6220403 : Nat := 4983230072969 + 3 ^ 40 * 6220403 * 2
def baseEnd_6220403 : Nat := 3194056603669531378355393

theorem tailTrace_6220403 : CollatzResearch.WordTrace tailWord_6220403 prefixEnd_6220403 3194056603669531378355393 := by
  unfold tailWord_6220403
  simp only [CollatzResearch.WordTrace]
  refine ⟨226876736083549766098689863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151251157389033177399126575 226876736083549766098689863)
  ·
    refine ⟨340315104125324649148034795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226876736083549766098689863 340315104125324649148034795)
    ·
      refine ⟨510472656187986973722052193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340315104125324649148034795 510472656187986973722052193)
      ·
        refine ⟨382854492140990230291539145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510472656187986973722052193 382854492140990230291539145)
        ·
          refine ⟨287140869105742672718654359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382854492140990230291539145 287140869105742672718654359)
          ·
            refine ⟨430711303658614009077981539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287140869105742672718654359 430711303658614009077981539)
            ·
              refine ⟨646066955487921013616972309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430711303658614009077981539 646066955487921013616972309)
              ·
                refine ⟨30284388538496297513295577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 646066955487921013616972309 30284388538496297513295577)
                ·
                  refine ⟨22713291403872223134971683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30284388538496297513295577 22713291403872223134971683)
                  ·
                    refine ⟨34069937105808334702457525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22713291403872223134971683 34069937105808334702457525)
                    ·
                      refine ⟨3194056603669531378355393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34069937105808334702457525 3194056603669531378355393)
                      ·
                        rfl

theorem cell23_6220403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_6220403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220403 prefixEnd_6220403 := by exact prefixLift 6220403
  have htrace : WordTrace (prefixWord ++ tailWord_6220403) baseStart_6220403 baseEnd_6220403 := by
    simpa [prefixWord, tailWord_6220403, baseEnd_6220403] using wordTrace_append hprefix tailTrace_6220403
  have hstable : (prefixWord ++ tailWord_6220403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220403).length < 2 ^ (prefixWord ++ tailWord_6220403).sum := by decide
  have hdescent : baseEnd_6220403 < baseStart_6220403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220417 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_6220417 : Nat := 118140960795 + 6220417 * 2 ^ 59
def prefixEnd_6220417 : Nat := 4983230072969 + 3 ^ 40 * 6220417 * 2
def baseEnd_6220417 : Nat := 3194063792398694323580329

theorem tailTrace_6220417 : CollatzResearch.WordTrace tailWord_6220417 prefixEnd_6220417 3194063792398694323580329 := by
  unfold tailWord_6220417
  simp only [CollatzResearch.WordTrace]
  refine ⟨226877246705499046489699505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151251497803666030993133003 226877246705499046489699505)
  ·
    refine ⟨170157935029124284867274629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226877246705499046489699505 170157935029124284867274629)
    ·
      refine ⟨31904612817960803412613993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170157935029124284867274629 31904612817960803412613993)
      ·
        refine ⟨23928459613470602559460495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31904612817960803412613993 23928459613470602559460495)
        ·
          refine ⟨35892689420205903839190743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23928459613470602559460495 35892689420205903839190743)
          ·
            refine ⟨53839034130308855758786115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35892689420205903839190743 53839034130308855758786115)
            ·
              refine ⟨80758551195463283638179173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53839034130308855758786115 80758551195463283638179173)
              ·
                refine ⟨15142228349149365682158595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80758551195463283638179173 15142228349149365682158595)
                ·
                  refine ⟨22713342523724048523237893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15142228349149365682158595 22713342523724048523237893)
                  ·
                    refine ⟨4258751723198259098107105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22713342523724048523237893 4258751723198259098107105)
                    ·
                      refine ⟨3194063792398694323580329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258751723198259098107105 3194063792398694323580329)
                      ·
                        rfl

theorem cell23_6220417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_6220417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220417 prefixEnd_6220417 := by exact prefixLift 6220417
  have htrace : WordTrace (prefixWord ++ tailWord_6220417) baseStart_6220417 baseEnd_6220417 := by
    simpa [prefixWord, tailWord_6220417, baseEnd_6220417] using wordTrace_append hprefix tailTrace_6220417
  have hstable : (prefixWord ++ tailWord_6220417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220417).length < 2 ^ (prefixWord ++ tailWord_6220417).sum := by decide
  have hdescent : baseEnd_6220417 < baseStart_6220417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220421 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_6220421 : Nat := 118140960795 + 6220421 * 2 ^ 59
def prefixEnd_6220421 : Nat := 4983230072969 + 3 ^ 40 * 6220421 * 2
def baseEnd_6220421 : Nat := 3194065846321312307930311

theorem tailTrace_6220421 : CollatzResearch.WordTrace tailWord_6220421 prefixEnd_6220421 3194065846321312307930311 := by
  unfold tailWord_6220421
  simp only [CollatzResearch.WordTrace]
  refine ⟨226877392597484555172845117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151251595064989703448563411 226877392597484555172845117)
  ·
    refine ⟨85079022224056708189816919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226877392597484555172845117 85079022224056708189816919)
    ·
      refine ⟨127618533336085062284725379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85079022224056708189816919 127618533336085062284725379)
      ·
        refine ⟨191427800004127593427088069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127618533336085062284725379 191427800004127593427088069)
        ·
          refine ⟨35892712500773923767579013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191427800004127593427088069 35892712500773923767579013)
          ·
            refine ⟨6729883593895110706421065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35892712500773923767579013 6729883593895110706421065)
            ·
              refine ⟨5047412695421333029815799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6729883593895110706421065 5047412695421333029815799)
              ·
                refine ⟨7571119043131999544723699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047412695421333029815799 7571119043131999544723699)
                ·
                  refine ⟨11356678564697999317085549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571119043131999544723699 11356678564697999317085549)
                  ·
                    refine ⟨4258754461761749743907081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11356678564697999317085549 4258754461761749743907081)
                    ·
                      refine ⟨3194065846321312307930311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258754461761749743907081 3194065846321312307930311)
                      ·
                        rfl

theorem cell23_6220421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_6220421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220421 prefixEnd_6220421 := by exact prefixLift 6220421
  have htrace : WordTrace (prefixWord ++ tailWord_6220421) baseStart_6220421 baseEnd_6220421 := by
    simpa [prefixWord, tailWord_6220421, baseEnd_6220421] using wordTrace_append hprefix tailTrace_6220421
  have hstable : (prefixWord ++ tailWord_6220421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220421).length < 2 ^ (prefixWord ++ tailWord_6220421).sum := by decide
  have hdescent : baseEnd_6220421 < baseStart_6220421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220423 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 9]
def baseStart_6220423 : Nat := 118140960795 + 6220423 * 2 ^ 59
def prefixEnd_6220423 : Nat := 4983230072969 + 3 ^ 40 * 6220423 * 2
def baseEnd_6220423 : Nat := 354896319253624588900589

theorem tailTrace_6220423 : CollatzResearch.WordTrace tailWord_6220423 prefixEnd_6220423 354896319253624588900589 := by
  unfold tailWord_6220423
  simp only [CollatzResearch.WordTrace]
  refine ⟨226877465543477309514417923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151251643695651539676278615 226877465543477309514417923)
  ·
    refine ⟨340316198315215964271626885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226877465543477309514417923 340316198315215964271626885)
    ·
      refine ⟨63809287184102993300930041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340316198315215964271626885 63809287184102993300930041)
      ·
        refine ⟨47856965388077244975697531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63809287184102993300930041 47856965388077244975697531)
        ·
          refine ⟨71785448082115867463546297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47856965388077244975697531 71785448082115867463546297)
          ·
            refine ⟨53839086061586900597659723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71785448082115867463546297 53839086061586900597659723)
            ·
              refine ⟨80758629092380350896489585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53839086061586900597659723 80758629092380350896489585)
              ·
                refine ⟨60568971819285263172367189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80758629092380350896489585 60568971819285263172367189)
                ·
                  refine ⟨354896319253624588900589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60568971819285263172367189 354896319253624588900589)
                  ·
                    rfl

theorem cell23_6220423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 9].length) (baseStart_6220423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220423 prefixEnd_6220423 := by exact prefixLift 6220423
  have htrace : WordTrace (prefixWord ++ tailWord_6220423) baseStart_6220423 baseEnd_6220423 := by
    simpa [prefixWord, tailWord_6220423, baseEnd_6220423] using wordTrace_append hprefix tailTrace_6220423
  have hstable : (prefixWord ++ tailWord_6220423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220423).length < 2 ^ (prefixWord ++ tailWord_6220423).sum := by decide
  have hdescent : baseEnd_6220423 < baseStart_6220423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220430 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6220430 : Nat := 118140960795 + 6220430 * 2 ^ 59
def prefixEnd_6220430 : Nat := 4983230072969 + 3 ^ 40 * 6220430 * 2
def baseEnd_6220430 : Nat := 3194070467647202772717769

theorem tailTrace_6220430 : CollatzResearch.WordTrace tailWord_6220430 prefixEnd_6220430 3194070467647202772717769 := by
  unfold tailWord_6220430
  simp only [CollatzResearch.WordTrace]
  refine ⟨28359715106806493713740343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151251813902967966473281829 28359715106806493713740343)
  ·
    refine ⟨42539572660209740570610515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28359715106806493713740343 42539572660209740570610515)
    ·
      refine ⟨63809358990314610855915773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42539572660209740570610515 63809358990314610855915773)
      ·
        refine ⟨23928509621367979070968415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63809358990314610855915773 23928509621367979070968415)
        ·
          refine ⟨35892764432051968606452623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23928509621367979070968415 35892764432051968606452623)
          ·
            refine ⟨53839146648077952909678935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35892764432051968606452623 53839146648077952909678935)
            ·
              refine ⟨80758719972116929364518403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53839146648077952909678935 80758719972116929364518403)
              ·
                refine ⟨121138079958175394046777605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80758719972116929364518403 121138079958175394046777605)
                ·
                  refine ⟨22713389992157886383770801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121138079958175394046777605 22713389992157886383770801)
                  ·
                    refine ⟨17035042494118414787828101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22713389992157886383770801 17035042494118414787828101)
                    ·
                      refine ⟨3194070467647202772717769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17035042494118414787828101 3194070467647202772717769)
                      ·
                        rfl

theorem cell23_6220430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6220430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220430 prefixEnd_6220430 := by exact prefixLift 6220430
  have htrace : WordTrace (prefixWord ++ tailWord_6220430) baseStart_6220430 baseEnd_6220430 := by
    simpa [prefixWord, tailWord_6220430, baseEnd_6220430] using wordTrace_append hprefix tailTrace_6220430
  have hstable : (prefixWord ++ tailWord_6220430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220430).length < 2 ^ (prefixWord ++ tailWord_6220430).sum := by decide
  have hdescent : baseEnd_6220430 < baseStart_6220430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220440 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 7]
def baseStart_6220440 : Nat := 118140960795 + 6220440 * 2 ^ 59
def prefixEnd_6220440 : Nat := 4983230072969 + 3 ^ 40 * 6220440 * 2
def baseEnd_6220440 : Nat := 354897289161527525954747

theorem tailTrace_6220440 : CollatzResearch.WordTrace tailWord_6220440 prefixEnd_6220440 354897289161527525954747 := by
  unfold tailWord_6220440
  simp only [CollatzResearch.WordTrace]
  refine ⟨113439042792207860708893387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151252057056277147611857849 113439042792207860708893387)
  ·
    refine ⟨170158564188311791063340081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113439042792207860708893387 170158564188311791063340081)
    ·
      refine ⟨127618923141233843297505061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170158564188311791063340081 127618923141233843297505061)
      ·
        refine ⟨23928548088981345618282199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127618923141233843297505061 23928548088981345618282199)
        ·
          refine ⟨35892822133472018427423299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23928548088981345618282199 35892822133472018427423299)
          ·
            refine ⟨53839233200208027641134949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35892822133472018427423299 53839233200208027641134949)
            ·
              refine ⟨10094856225039005182712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53839233200208027641134949 10094856225039005182712803)
              ·
                refine ⟨15142284337558507774069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10094856225039005182712803 15142284337558507774069205)
                ·
                  refine ⟨354897289161527525954747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15142284337558507774069205 354897289161527525954747)
                  ·
                    rfl

theorem cell23_6220440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_6220440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220440 prefixEnd_6220440 := by exact prefixLift 6220440
  have htrace : WordTrace (prefixWord ++ tailWord_6220440) baseStart_6220440 baseEnd_6220440 := by
    simpa [prefixWord, tailWord_6220440, baseEnd_6220440] using wordTrace_append hprefix tailTrace_6220440
  have hstable : (prefixWord ++ tailWord_6220440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220440).length < 2 ^ (prefixWord ++ tailWord_6220440).sum := by decide
  have hdescent : baseEnd_6220440 < baseStart_6220440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220527 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_6220527 : Nat := 118140960795 + 6220527 * 2 ^ 59
def prefixEnd_6220527 : Nat := 4983230072969 + 3 ^ 40 * 6220527 * 2
def baseEnd_6220527 : Nat := 3194120275270688893204823

theorem tailTrace_6220527 : CollatzResearch.WordTrace tailWord_6220527 prefixEnd_6220527 3194120275270688893204823 := by
  unfold tailWord_6220527
  simp only [CollatzResearch.WordTrace]
  refine ⟨226881258735100535276203835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151254172490067023517469223 226881258735100535276203835)
  ·
    refine ⟨340321888102650802914305753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226881258735100535276203835 340321888102650802914305753)
    ·
      refine ⟨255241416076988102185729315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340321888102650802914305753 255241416076988102185729315)
      ·
        refine ⟨382862124115482153278593973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255241416076988102185729315 382862124115482153278593973)
        ·
          refine ⟨35893324135826451869868185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382862124115482153278593973 35893324135826451869868185)
          ·
            refine ⟨26919993101869838902401139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35893324135826451869868185 26919993101869838902401139)
            ·
              refine ⟨40379989652804758353601709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26919993101869838902401139 40379989652804758353601709)
              ·
                refine ⟨15142496119801784382600641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40379989652804758353601709 15142496119801784382600641)
                ·
                  refine ⟨11356872089851338286950481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15142496119801784382600641 11356872089851338286950481)
                  ·
                    refine ⟨8517654067388503715212861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11356872089851338286950481 8517654067388503715212861)
                    ·
                      refine ⟨3194120275270688893204823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517654067388503715212861 3194120275270688893204823)
                      ·
                        rfl

theorem cell23_6220527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_6220527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220527 prefixEnd_6220527 := by exact prefixLift 6220527
  have htrace : WordTrace (prefixWord ++ tailWord_6220527) baseStart_6220527 baseEnd_6220527 := by
    simpa [prefixWord, tailWord_6220527, baseEnd_6220527] using wordTrace_append hprefix tailTrace_6220527
  have hstable : (prefixWord ++ tailWord_6220527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220527).length < 2 ^ (prefixWord ++ tailWord_6220527).sum := by decide
  have hdescent : baseEnd_6220527 < baseStart_6220527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220551 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 1, 4]
def baseStart_6220551 : Nat := 118140960795 + 6220551 * 2 ^ 59
def prefixEnd_6220551 : Nat := 4983230072969 + 3 ^ 40 * 6220551 * 2
def baseEnd_6220551 : Nat := 1064710866268798933101571

theorem tailTrace_6220551 : CollatzResearch.WordTrace tailWord_6220551 prefixEnd_6220551 1064710866268798933101571 := by
  unfold tailWord_6220551
  simp only [CollatzResearch.WordTrace]
  refine ⟨226882134087013587375077507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151254756058009058250051671 226882134087013587375077507)
  ·
    refine ⟨340323201130520381062616261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226882134087013587375077507 340323201130520381062616261)
    ·
      refine ⟨63810600211972571449240549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340323201130520381062616261 63810600211972571449240549)
      ·
        refine ⟨11964487539744857146732603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63810600211972571449240549 11964487539744857146732603)
        ·
          refine ⟨17946731309617285720098905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11964487539744857146732603 17946731309617285720098905)
          ·
            refine ⟨13460048482212964290074179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17946731309617285720098905 13460048482212964290074179)
            ·
              refine ⟨20190072723319446435111269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460048482212964290074179 20190072723319446435111269)
              ·
                refine ⟨3785638635622396206583363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20190072723319446435111269 3785638635622396206583363)
                ·
                  refine ⟨5678457953433594309875045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785638635622396206583363 5678457953433594309875045)
                  ·
                    refine ⟨1064710866268798933101571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678457953433594309875045 1064710866268798933101571)
                    ·
                      rfl

theorem cell23_6220551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_6220551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220551 prefixEnd_6220551 := by exact prefixLift 6220551
  have htrace : WordTrace (prefixWord ++ tailWord_6220551) baseStart_6220551 baseEnd_6220551 := by
    simpa [prefixWord, tailWord_6220551, baseEnd_6220551] using wordTrace_append hprefix tailTrace_6220551
  have hstable : (prefixWord ++ tailWord_6220551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220551).length < 2 ^ (prefixWord ++ tailWord_6220551).sum := by decide
  have hdescent : baseEnd_6220551 < baseStart_6220551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220570 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_6220570 : Nat := 118140960795 + 6220570 * 2 ^ 59
def prefixEnd_6220570 : Nat := 4983230072969 + 3 ^ 40 * 6220570 * 2
def baseEnd_6220570 : Nat := 3194142354938832224967125

theorem tailTrace_6220570 : CollatzResearch.WordTrace tailWord_6220570 prefixEnd_6220570 3194142354938832224967125 := by
  unfold tailWord_6220570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56720706768486188405004791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151255218049296502413346109 56720706768486188405004791)
  ·
    refine ⟨85081060152729282607507187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56720706768486188405004791 85081060152729282607507187)
    ·
      refine ⟨127621590229093923911260781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85081060152729282607507187 127621590229093923911260781)
      ·
        refine ⟨47858096335910221466722793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127621590229093923911260781 47858096335910221466722793)
        ·
          refine ⟨35893572251932666100042095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47858096335910221466722793 35893572251932666100042095)
          ·
            refine ⟨53840358377898999150063143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35893572251932666100042095 53840358377898999150063143)
            ·
              refine ⟨80760537566848498725094715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53840358377898999150063143 80760537566848498725094715)
              ·
                refine ⟨121140806350272748087642073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80760537566848498725094715 121140806350272748087642073)
                ·
                  refine ⟨90855604762704561065731555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121140806350272748087642073 90855604762704561065731555)
                  ·
                    refine ⟨136283407144056841598597333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90855604762704561065731555 136283407144056841598597333)
                    ·
                      refine ⟨3194142354938832224967125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136283407144056841598597333 3194142354938832224967125)
                      ·
                        rfl

theorem cell23_6220570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_6220570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220570 prefixEnd_6220570 := by exact prefixLift 6220570
  have htrace : WordTrace (prefixWord ++ tailWord_6220570) baseStart_6220570 baseEnd_6220570 := by
    simpa [prefixWord, tailWord_6220570, baseEnd_6220570] using wordTrace_append hprefix tailTrace_6220570
  have hstable : (prefixWord ++ tailWord_6220570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220570).length < 2 ^ (prefixWord ++ tailWord_6220570).sum := by decide
  have hdescent : baseEnd_6220570 < baseStart_6220570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220577 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_6220577 : Nat := 118140960795 + 6220577 * 2 ^ 59
def prefixEnd_6220577 : Nat := 4983230072969 + 3 ^ 40 * 6220577 * 2
def baseEnd_6220577 : Nat := 1064715316434471232526531

theorem tailTrace_6220577 : CollatzResearch.WordTrace tailWord_6220577 prefixEnd_6220577 1064715316434471232526531 := by
  unfold tailWord_6220577
  simp only [CollatzResearch.WordTrace]
  refine ⟨226883082384919393815523985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151255388256612929210349323 226883082384919393815523985)
  ·
    refine ⟨170162311788689545361642989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226883082384919393815523985 170162311788689545361642989)
    ·
      refine ⟨63810866920758579510616121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170162311788689545361642989 63810866920758579510616121)
      ·
        refine ⟨47858150190568934632962091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63810866920758579510616121 47858150190568934632962091)
        ·
          refine ⟨71787225285853401949443137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47858150190568934632962091 71787225285853401949443137)
          ·
            refine ⟨53840418964390051462082353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71787225285853401949443137 53840418964390051462082353)
            ·
              refine ⟨40380314223292538596561765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53840418964390051462082353 40380314223292538596561765)
              ·
                refine ⟨7571308916867350986855331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40380314223292538596561765 7571308916867350986855331)
                ·
                  refine ⟨11356963375301026480282997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571308916867350986855331 11356963375301026480282997)
                  ·
                    refine ⟨1064715316434471232526531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11356963375301026480282997 1064715316434471232526531)
                    ·
                      rfl

theorem cell23_6220577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_6220577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220577 prefixEnd_6220577 := by exact prefixLift 6220577
  have htrace : WordTrace (prefixWord ++ tailWord_6220577) baseStart_6220577 baseEnd_6220577 := by
    simpa [prefixWord, tailWord_6220577, baseEnd_6220577] using wordTrace_append hprefix tailTrace_6220577
  have hstable : (prefixWord ++ tailWord_6220577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220577).length < 2 ^ (prefixWord ++ tailWord_6220577).sum := by decide
  have hdescent : baseEnd_6220577 < baseStart_6220577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220584 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_6220584 : Nat := 118140960795 + 6220584 * 2 ^ 59
def prefixEnd_6220584 : Nat := 4983230072969 + 3 ^ 40 * 6220584 * 2
def baseEnd_6220584 : Nat := 3194149543667995170192061

theorem tailTrace_6220584 : CollatzResearch.WordTrace tailWord_6220584 prefixEnd_6220584 3194149543667995170192061 := by
  unfold tailWord_6220584
  simp only [CollatzResearch.WordTrace]
  refine ⟨113441668847947017005514403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151255558463929356007352537 113441668847947017005514403)
  ·
    refine ⟨170162503271920525508271605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113441668847947017005514403 170162503271920525508271605)
    ·
      refine ⟨15952734681742549266400463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170162503271920525508271605 15952734681742549266400463)
      ·
        refine ⟨23929102022613823899600695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15952734681742549266400463 23929102022613823899600695)
        ·
          refine ⟨35893653033920735849401043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23929102022613823899600695 35893653033920735849401043)
          ·
            refine ⟨53840479550881103774101565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35893653033920735849401043 53840479550881103774101565)
            ·
              refine ⟨20190179831580413915288087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53840479550881103774101565 20190179831580413915288087)
              ·
                refine ⟨30285269747370620872932131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190179831580413915288087 30285269747370620872932131)
                ·
                  refine ⟨45427904621055931309398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30285269747370620872932131 45427904621055931309398197)
                  ·
                    refine ⟨4258866058223993560256081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45427904621055931309398197 4258866058223993560256081)
                    ·
                      refine ⟨3194149543667995170192061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258866058223993560256081 3194149543667995170192061)
                      ·
                        rfl

theorem cell23_6220584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_6220584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220584 prefixEnd_6220584 := by exact prefixLift 6220584
  have htrace : WordTrace (prefixWord ++ tailWord_6220584) baseStart_6220584 baseEnd_6220584 := by
    simpa [prefixWord, tailWord_6220584, baseEnd_6220584] using wordTrace_append hprefix tailTrace_6220584
  have hstable : (prefixWord ++ tailWord_6220584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220584).length < 2 ^ (prefixWord ++ tailWord_6220584).sum := by decide
  have hdescent : baseEnd_6220584 < baseStart_6220584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220598 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_6220598 : Nat := 118140960795 + 6220598 * 2 ^ 59
def prefixEnd_6220598 : Nat := 4983230072969 + 3 ^ 40 * 6220598 * 2
def baseEnd_6220598 : Nat := 354906303599684235046333

theorem tailTrace_6220598 : CollatzResearch.WordTrace tailWord_6220598 prefixEnd_6220598 354906303599684235046333 := by
  unfold tailWord_6220598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180240519865207150127403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151255898878562209601358965 14180240519865207150127403)
  ·
    refine ⟨21270360779797810725191105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14180240519865207150127403 21270360779797810725191105)
    ·
      refine ⟨15952770584848358043893329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21270360779797810725191105 15952770584848358043893329)
      ·
        refine ⟨11964577938636268532919997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15952770584848358043893329 11964577938636268532919997)
        ·
          refine ⟨4486716726988600699844999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11964577938636268532919997 4486716726988600699844999)
          ·
            refine ⟨6730075090482901049767499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486716726988600699844999 6730075090482901049767499)
            ·
              refine ⟨10095112635724351574651249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730075090482901049767499 10095112635724351574651249)
              ·
                refine ⟨7571334476793263680988437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10095112635724351574651249 7571334476793263680988437)
                ·
                  refine ⟨354906303599684235046333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7571334476793263680988437 354906303599684235046333)
                  ·
                    rfl

theorem cell23_6220598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_6220598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220598 prefixEnd_6220598 := by exact prefixLift 6220598
  have htrace : WordTrace (prefixWord ++ tailWord_6220598) baseStart_6220598 baseEnd_6220598 := by
    simpa [prefixWord, tailWord_6220598, baseEnd_6220598] using wordTrace_append hprefix tailTrace_6220598
  have hstable : (prefixWord ++ tailWord_6220598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220598).length < 2 ^ (prefixWord ++ tailWord_6220598).sum := by decide
  have hdescent : baseEnd_6220598 < baseStart_6220598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220617 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_6220617 : Nat := 118140960795 + 6220617 * 2 ^ 59
def prefixEnd_6220617 : Nat := 4983230072969 + 3 ^ 40 * 6220617 * 2
def baseEnd_6220617 : Nat := 3194166488529593541079409

theorem tailTrace_6220617 : CollatzResearch.WordTrace tailWord_6220617 prefixEnd_6220617 3194166488529593541079409 := by
  unfold tailWord_6220617
  simp only [CollatzResearch.WordTrace]
  refine ⟨226884541304774480646980105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151256360869849653764653403 226884541304774480646980105)
  ·
    refine ⟨170163405978580860485235079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226884541304774480646980105 170163405978580860485235079)
    ·
      refine ⟨255245108967871290727852619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170163405978580860485235079 255245108967871290727852619)
      ·
        refine ⟨382867663451806936091778929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255245108967871290727852619 382867663451806936091778929)
        ·
          refine ⟨287150747588855202068834197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382867663451806936091778929 287150747588855202068834197)
          ·
            refine ⟨13460191293227587596976603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287150747588855202068834197 13460191293227587596976603)
            ·
              refine ⟨20190286939841381395464905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460191293227587596976603 20190286939841381395464905)
              ·
                refine ⟨15142715204881036046598679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20190286939841381395464905 15142715204881036046598679)
                ·
                  refine ⟨22714072807321554069898019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15142715204881036046598679 22714072807321554069898019)
                  ·
                    refine ⟨34071109210982331104847029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22714072807321554069898019 34071109210982331104847029)
                    ·
                      refine ⟨3194166488529593541079409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34071109210982331104847029 3194166488529593541079409)
                      ·
                        rfl

theorem cell23_6220617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_6220617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220617 prefixEnd_6220617 := by exact prefixLift 6220617
  have htrace : WordTrace (prefixWord ++ tailWord_6220617) baseStart_6220617 baseEnd_6220617 := by
    simpa [prefixWord, tailWord_6220617, baseEnd_6220617] using wordTrace_append hprefix tailTrace_6220617
  have hstable : (prefixWord ++ tailWord_6220617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220617).length < 2 ^ (prefixWord ++ tailWord_6220617).sum := by decide
  have hdescent : baseEnd_6220617 < baseStart_6220617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220631 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_6220631 : Nat := 118140960795 + 6220631 * 2 ^ 59
def prefixEnd_6220631 : Nat := 4983230072969 + 3 ^ 40 * 6220631 * 2
def baseEnd_6220631 : Nat := 3194173677258756486304345

theorem tailTrace_6220631 : CollatzResearch.WordTrace tailWord_6220631 prefixEnd_6220631 3194173677258756486304345 := by
  unfold tailWord_6220631
  simp only [CollatzResearch.WordTrace]
  refine ⟨226885051926723761037989747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151256701284482507358659831 226885051926723761037989747)
  ·
    refine ⟨340327577890085641556984621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226885051926723761037989747 340327577890085641556984621)
    ·
      refine ⟨127622841708782115583869233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340327577890085641556984621 127622841708782115583869233)
      ·
        refine ⟨95717131281586586687901925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127622841708782115583869233 95717131281586586687901925)
        ·
          refine ⟨17946962115297485003981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95717131281586586687901925 17946962115297485003981611)
          ·
            refine ⟨26920443172946227505972417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17946962115297485003981611 26920443172946227505972417)
            ·
              refine ⟨20190332379709670629479313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26920443172946227505972417 20190332379709670629479313)
              ·
                refine ⟨15142749284782252972109485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20190332379709670629479313 15142749284782252972109485)
                ·
                  refine ⟨5678530981793344864541057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15142749284782252972109485 5678530981793344864541057)
                  ·
                    refine ⟨4258898236345008648405793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5678530981793344864541057 4258898236345008648405793)
                    ·
                      refine ⟨3194173677258756486304345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258898236345008648405793 3194173677258756486304345)
                      ·
                        rfl

theorem cell23_6220631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_6220631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220631 prefixEnd_6220631 := by exact prefixLift 6220631
  have htrace : WordTrace (prefixWord ++ tailWord_6220631) baseStart_6220631 baseEnd_6220631 := by
    simpa [prefixWord, tailWord_6220631, baseEnd_6220631] using wordTrace_append hprefix tailTrace_6220631
  have hstable : (prefixWord ++ tailWord_6220631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220631).length < 2 ^ (prefixWord ++ tailWord_6220631).sum := by decide
  have hdescent : baseEnd_6220631 < baseStart_6220631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220634 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_6220634 : Nat := 118140960795 + 6220634 * 2 ^ 59
def prefixEnd_6220634 : Nat := 4983230072969 + 3 ^ 40 * 6220634 * 2
def baseEnd_6220634 : Nat := 3194175217700719974566831

theorem tailTrace_6220634 : CollatzResearch.WordTrace tailWord_6220634 prefixEnd_6220634 3194175217700719974566831 := by
  unfold tailWord_6220634
  simp only [CollatzResearch.WordTrace]
  refine ⟨56721290336428223137587239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151256774230475261700232637 56721290336428223137587239)
  ·
    refine ⟨85081935504642334706380859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56721290336428223137587239 85081935504642334706380859)
    ·
      refine ⟨127622903256963502059571289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85081935504642334706380859 127622903256963502059571289)
      ·
        refine ⟨95717177442722626544678467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127622903256963502059571289 95717177442722626544678467)
        ·
          refine ⟨143575766164083939817017701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95717177442722626544678467 143575766164083939817017701)
          ·
            refine ⟨26920456155765738715690819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143575766164083939817017701 26920456155765738715690819)
            ·
              refine ⟨40380684233648608073536229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26920456155765738715690819 40380684233648608073536229)
              ·
                refine ⟨7571378293809114013788043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40380684233648608073536229 7571378293809114013788043)
                ·
                  refine ⟨11357067440713671020682065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571378293809114013788043 11357067440713671020682065)
                  ·
                    refine ⟨8517800580535253265511549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11357067440713671020682065 8517800580535253265511549)
                    ·
                      refine ⟨3194175217700719974566831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517800580535253265511549 3194175217700719974566831)
                      ·
                        rfl

theorem cell23_6220634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_6220634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220634 prefixEnd_6220634 := by exact prefixLift 6220634
  have htrace : WordTrace (prefixWord ++ tailWord_6220634) baseStart_6220634 baseEnd_6220634 := by
    simpa [prefixWord, tailWord_6220634, baseEnd_6220634] using wordTrace_append hprefix tailTrace_6220634
  have hstable : (prefixWord ++ tailWord_6220634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220634).length < 2 ^ (prefixWord ++ tailWord_6220634).sum := by decide
  have hdescent : baseEnd_6220634 < baseStart_6220634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220642 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6220642 : Nat := 118140960795 + 6220642 * 2 ^ 59
def prefixEnd_6220642 : Nat := 4983230072969 + 3 ^ 40 * 6220642 * 2
def baseEnd_6220642 : Nat := 3194179325545955943266795

theorem tailTrace_6220642 : CollatzResearch.WordTrace tailWord_6220642 prefixEnd_6220642 3194179325545955943266795 := by
  unfold tailWord_6220642
  simp only [CollatzResearch.WordTrace]
  refine ⟨56721363282420977479160045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151256968753122606611093453 56721363282420977479160045)
  ·
    refine ⟨21270511230907866554685017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56721363282420977479160045 21270511230907866554685017)
    ·
      refine ⟨15952883423180899916013763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21270511230907866554685017 15952883423180899916013763)
      ·
        refine ⟨23929325134771349874020645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15952883423180899916013763 23929325134771349874020645)
        ·
          refine ⟨4486748462769628101378871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23929325134771349874020645 4486748462769628101378871)
          ·
            refine ⟨6730122694154442152068307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4486748462769628101378871 6730122694154442152068307)
            ·
              refine ⟨10095184041231663228102461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730122694154442152068307 10095184041231663228102461)
              ·
                refine ⟨3785694015461873710538423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10095184041231663228102461 3785694015461873710538423)
                ·
                  refine ⟨5678541023192810565807635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785694015461873710538423 5678541023192810565807635)
                  ·
                    refine ⟨8517811534789215848711453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5678541023192810565807635 8517811534789215848711453)
                    ·
                      refine ⟨3194179325545955943266795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517811534789215848711453 3194179325545955943266795)
                      ·
                        rfl

theorem cell23_6220642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6220642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220642 prefixEnd_6220642 := by exact prefixLift 6220642
  have htrace : WordTrace (prefixWord ++ tailWord_6220642) baseStart_6220642 baseEnd_6220642 := by
    simpa [prefixWord, tailWord_6220642, baseEnd_6220642] using wordTrace_append hprefix tailTrace_6220642
  have hstable : (prefixWord ++ tailWord_6220642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220642).length < 2 ^ (prefixWord ++ tailWord_6220642).sum := by decide
  have hdescent : baseEnd_6220642 < baseStart_6220642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220654 : List Nat := [4, 1, 2, 3, 2, 2, 9]
def baseStart_6220654 : Nat := 118140960795 + 6220654 * 2 ^ 59
def prefixEnd_6220654 : Nat := 4983230072969 + 3 ^ 40 * 6220654 * 2
def baseEnd_6220654 : Nat := 39434388732269257979219

theorem tailTrace_6220654 : CollatzResearch.WordTrace tailWord_6220654 prefixEnd_6220654 39434388732269257979219 := by
  unfold tailWord_6220654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28360736350705054495759627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151257260537093623977384677 28360736350705054495759627)
  ·
    refine ⟨42541104526057581743639441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28360736350705054495759627 42541104526057581743639441)
    ·
      refine ⟨31905828394543186307729581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42541104526057581743639441 31905828394543186307729581)
      ·
        refine ⟨11964685647953694865398593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31905828394543186307729581 11964685647953694865398593)
        ·
          refine ⟨8973514235965271149048945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11964685647953694865398593 8973514235965271149048945)
          ·
            refine ⟨6730135676973953361786709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8973514235965271149048945 6730135676973953361786709)
            ·
              refine ⟨39434388732269257979219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6730135676973953361786709 39434388732269257979219)
              ·
                rfl

theorem cell23_6220654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 9].length) (baseStart_6220654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220654 prefixEnd_6220654 := by exact prefixLift 6220654
  have htrace : WordTrace (prefixWord ++ tailWord_6220654) baseStart_6220654 baseEnd_6220654 := by
    simpa [prefixWord, tailWord_6220654, baseEnd_6220654] using wordTrace_append hprefix tailTrace_6220654
  have hstable : (prefixWord ++ tailWord_6220654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220654).length < 2 ^ (prefixWord ++ tailWord_6220654).sum := by decide
  have hdescent : baseEnd_6220654 < baseStart_6220654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220665 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 1, 2, 2]
def baseStart_6220665 : Nat := 118140960795 + 6220665 * 2 ^ 59
def prefixEnd_6220665 : Nat := 4983230072969 + 3 ^ 40 * 6220665 * 2
def baseEnd_6220665 : Nat := 3194191135601009353279189

theorem tailTrace_6220665 : CollatzResearch.WordTrace tailWord_6220665 prefixEnd_6220665 3194191135601009353279189 := by
  unfold tailWord_6220665
  simp only [CollatzResearch.WordTrace]
  refine ⟨226886292008600584844727449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151257528005733723229818299 226886292008600584844727449)
  ·
    refine ⟨170164719006450438633545587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226886292008600584844727449 170164719006450438633545587)
    ·
      refine ⟨255247078509675657950318381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170164719006450438633545587 255247078509675657950318381)
      ·
        refine ⟨95717654441128371731369393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255247078509675657950318381 95717654441128371731369393)
        ·
          refine ⟨71788240830846278798527045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95717654441128371731369393 71788240830846278798527045)
          ·
            refine ⟨13460295155783677274723821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71788240830846278798527045 13460295155783677274723821)
            ·
              refine ⟨5047610683418878978021433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13460295155783677274723821 5047610683418878978021433)
              ·
                refine ⟨3785708012564159233516075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5047610683418878978021433 3785708012564159233516075)
                ·
                  refine ⟨5678562018846238850274113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785708012564159233516075 5678562018846238850274113)
                  ·
                    refine ⟨4258921514134679137705585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5678562018846238850274113 4258921514134679137705585)
                    ·
                      refine ⟨3194191135601009353279189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258921514134679137705585 3194191135601009353279189)
                      ·
                        rfl

theorem cell23_6220665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_6220665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220665 prefixEnd_6220665 := by exact prefixLift 6220665
  have htrace : WordTrace (prefixWord ++ tailWord_6220665) baseStart_6220665 baseEnd_6220665 := by
    simpa [prefixWord, tailWord_6220665, baseEnd_6220665] using wordTrace_append hprefix tailTrace_6220665
  have hstable : (prefixWord ++ tailWord_6220665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220665).length < 2 ^ (prefixWord ++ tailWord_6220665).sum := by decide
  have hdescent : baseEnd_6220665 < baseStart_6220665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220681 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 3]
def baseStart_6220681 : Nat := 118140960795 + 6220681 * 2 ^ 59
def prefixEnd_6220681 : Nat := 4983230072969 + 3 ^ 40 * 6220681 * 2
def baseEnd_6220681 : Nat := 3194199351291481290679115

theorem tailTrace_6220681 : CollatzResearch.WordTrace tailWord_6220681 prefixEnd_6220681 3194199351291481290679115 := by
  unfold tailWord_6220681
  simp only [CollatzResearch.WordTrace]
  refine ⟨226886875576542619577309897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151257917051028413051539931 226886875576542619577309897)
  ·
    refine ⟨170165156682406964682982423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226886875576542619577309897 170165156682406964682982423)
    ·
      refine ⟨255247735023610447024473635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170165156682406964682982423 255247735023610447024473635)
      ·
        refine ⟨382871602535415670536710453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255247735023610447024473635 382871602535415670536710453)
        ·
          refine ⟨35894212737695219112816605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382871602535415670536710453 35894212737695219112816605)
          ·
            refine ⟨13460329776635707167306227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35894212737695219112816605 13460329776635707167306227)
            ·
              refine ⟨20190494664953560750959341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460329776635707167306227 20190494664953560750959341)
              ·
                refine ⟨7571435499357585281609753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20190494664953560750959341 7571435499357585281609753)
                ·
                  refine ⟨5678576624518188961207315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7571435499357585281609753 5678576624518188961207315)
                  ·
                    refine ⟨8517864936777283441810973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5678576624518188961207315 8517864936777283441810973)
                    ·
                      refine ⟨3194199351291481290679115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8517864936777283441810973 3194199351291481290679115)
                      ·
                        rfl

theorem cell23_6220681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_6220681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220681 prefixEnd_6220681 := by exact prefixLift 6220681
  have htrace : WordTrace (prefixWord ++ tailWord_6220681) baseStart_6220681 baseEnd_6220681 := by
    simpa [prefixWord, tailWord_6220681, baseEnd_6220681] using wordTrace_append hprefix tailTrace_6220681
  have hstable : (prefixWord ++ tailWord_6220681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220681).length < 2 ^ (prefixWord ++ tailWord_6220681).sum := by decide
  have hdescent : baseEnd_6220681 < baseStart_6220681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220704 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2]
def baseStart_6220704 : Nat := 118140960795 + 6220704 * 2 ^ 59
def prefixEnd_6220704 : Nat := 4983230072969 + 3 ^ 40 * 6220704 * 2
def baseEnd_6220704 : Nat := 3194211161346534700691509

theorem tailTrace_6220704 : CollatzResearch.WordTrace tailWord_6220704 prefixEnd_6220704 3194211161346534700691509 := by
  unfold tailWord_6220704
  simp only [CollatzResearch.WordTrace]
  refine ⟨113443857227729647252698583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151258476303639529670264777 113443857227729647252698583)
  ·
    refine ⟨170165785841594470879047875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113443857227729647252698583 170165785841594470879047875)
    ·
      refine ⟨255248678762391706318571813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170165785841594470879047875 255248678762391706318571813)
      ·
        refine ⟨47859127267948444934732215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255248678762391706318571813 47859127267948444934732215)
        ·
          refine ⟨71788690901922667402098323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47859127267948444934732215 71788690901922667402098323)
          ·
            refine ⟨107683036352884001103147485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71788690901922667402098323 107683036352884001103147485)
            ·
              refine ⟨40381138632331500413680307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107683036352884001103147485 40381138632331500413680307)
              ·
                refine ⟨60571707948497250620520461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40381138632331500413680307 60571707948497250620520461)
                ·
                  refine ⟨22714390480686468982695173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60571707948497250620520461 22714390480686468982695173)
                  ·
                    refine ⟨4258948215128712934255345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22714390480686468982695173 4258948215128712934255345)
                    ·
                      refine ⟨3194211161346534700691509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258948215128712934255345 3194211161346534700691509)
                      ·
                        rfl

theorem cell23_6220704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_6220704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220704 prefixEnd_6220704 := by exact prefixLift 6220704
  have htrace : WordTrace (prefixWord ++ tailWord_6220704) baseStart_6220704 baseEnd_6220704 := by
    simpa [prefixWord, tailWord_6220704, baseEnd_6220704] using wordTrace_append hprefix tailTrace_6220704
  have hstable : (prefixWord ++ tailWord_6220704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220704).length < 2 ^ (prefixWord ++ tailWord_6220704).sum := by decide
  have hdescent : baseEnd_6220704 < baseStart_6220704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220707 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_6220707 : Nat := 118140960795 + 6220707 * 2 ^ 59
def prefixEnd_6220707 : Nat := 4983230072969 + 3 ^ 40 * 6220707 * 2
def baseEnd_6220707 : Nat := 3194212701788498188953995

theorem tailTrace_6220707 : CollatzResearch.WordTrace tailWord_6220707 prefixEnd_6220707 3194212701788498188953995 := by
  unfold tailWord_6220707
  simp only [CollatzResearch.WordTrace]
  refine ⟨226887823874448426017756375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151258549249632284011837583 226887823874448426017756375)
  ·
    refine ⟨340331735811672639026634563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226887823874448426017756375 340331735811672639026634563)
    ·
      refine ⟨510497603717508958539951845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340331735811672639026634563 510497603717508958539951845)
      ·
        refine ⟨95718300697032929726240971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 510497603717508958539951845 95718300697032929726240971)
        ·
          refine ⟨143577451045549394589361457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95718300697032929726240971 143577451045549394589361457)
          ·
            refine ⟨107683088284162045942021093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143577451045549394589361457 107683088284162045942021093)
            ·
              refine ⟨20190579053280383614128955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107683088284162045942021093 20190579053280383614128955)
              ·
                refine ⟨30285868579920575421193433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190579053280383614128955 30285868579920575421193433)
                ·
                  refine ⟨22714401434940431565895075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30285868579920575421193433 22714401434940431565895075)
                  ·
                    refine ⟨34071602152410647348842613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22714401434940431565895075 34071602152410647348842613)
                    ·
                      refine ⟨3194212701788498188953995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34071602152410647348842613 3194212701788498188953995)
                      ·
                        rfl

theorem cell23_6220707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_6220707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220707 prefixEnd_6220707 := by exact prefixLift 6220707
  have htrace : WordTrace (prefixWord ++ tailWord_6220707) baseStart_6220707 baseEnd_6220707 := by
    simpa [prefixWord, tailWord_6220707, baseEnd_6220707] using wordTrace_append hprefix tailTrace_6220707
  have hstable : (prefixWord ++ tailWord_6220707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220707).length < 2 ^ (prefixWord ++ tailWord_6220707).sum := by decide
  have hdescent : baseEnd_6220707 < baseStart_6220707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220708 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_6220708 : Nat := 118140960795 + 6220708 * 2 ^ 59
def prefixEnd_6220708 : Nat := 4983230072969 + 3 ^ 40 * 6220708 * 2
def baseEnd_6220708 : Nat := 3194213215269152685041491

theorem tailTrace_6220708 : CollatzResearch.WordTrace tailWord_6220708 prefixEnd_6220708 3194213215269152685041491 := by
  unfold tailWord_6220708
  simp only [CollatzResearch.WordTrace]
  refine ⟨113443930173722401594271389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151258573564963202125695185 113443930173722401594271389)
  ·
    refine ⟨42541473815145900597851771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113443930173722401594271389 42541473815145900597851771)
    ·
      refine ⟨63812210722718850896777657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42541473815145900597851771 63812210722718850896777657)
      ·
        refine ⟨47859158042039138172583243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63812210722718850896777657 47859158042039138172583243)
        ·
          refine ⟨71788737063058707258874865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47859158042039138172583243 71788737063058707258874865)
          ·
            refine ⟨53841552797294030444156149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71788737063058707258874865 53841552797294030444156149)
            ·
              refine ⟨5047645574746315354139639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53841552797294030444156149 5047645574746315354139639)
              ·
                refine ⟨7571468362119473031209459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047645574746315354139639 7571468362119473031209459)
                ·
                  refine ⟨11357202543179209546814189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571468362119473031209459 11357202543179209546814189)
                  ·
                    refine ⟨4258950953692203580055321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11357202543179209546814189 4258950953692203580055321)
                    ·
                      refine ⟨3194213215269152685041491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4258950953692203580055321 3194213215269152685041491)
                      ·
                        rfl

theorem cell23_6220708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_6220708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220708 prefixEnd_6220708 := by exact prefixLift 6220708
  have htrace : WordTrace (prefixWord ++ tailWord_6220708) baseStart_6220708 baseEnd_6220708 := by
    simpa [prefixWord, tailWord_6220708, baseEnd_6220708] using wordTrace_append hprefix tailTrace_6220708
  have hstable : (prefixWord ++ tailWord_6220708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220708).length < 2 ^ (prefixWord ++ tailWord_6220708).sum := by decide
  have hdescent : baseEnd_6220708 < baseStart_6220708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220734 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_6220734 : Nat := 118140960795 + 6220734 * 2 ^ 59
def prefixEnd_6220734 : Nat := 4983230072969 + 3 ^ 40 * 6220734 * 2
def baseEnd_6220734 : Nat := 3194226565766169583316371

theorem tailTrace_6220734 : CollatzResearch.WordTrace tailWord_6220734 prefixEnd_6220734 3194226565766169583316371 := by
  unfold tailWord_6220734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28361101080668826203623657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151259205763567073085992837 28361101080668826203623657)
  ·
    refine ⟨21270825810501619652717743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28361101080668826203623657 21270825810501619652717743)
    ·
      refine ⟨31906238715752429479076615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21270825810501619652717743 31906238715752429479076615)
      ·
        refine ⟨47859358073628644218614923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31906238715752429479076615 47859358073628644218614923)
        ·
          refine ⟨71789037110442966327922385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47859358073628644218614923 71789037110442966327922385)
          ·
            refine ⟨53841777832832224745941789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71789037110442966327922385 53841777832832224745941789)
            ·
              refine ⟨20190666687312084279728171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53841777832832224745941789 20190666687312084279728171)
              ·
                refine ⟨30286000030968126419592257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190666687312084279728171 30286000030968126419592257)
                ·
                  refine ⟨22714500023226094814694193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30286000030968126419592257 22714500023226094814694193)
                  ·
                    refine ⟨17035875017419571111020645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22714500023226094814694193 17035875017419571111020645)
                    ·
                      refine ⟨3194226565766169583316371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17035875017419571111020645 3194226565766169583316371)
                      ·
                        rfl

theorem cell23_6220734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_6220734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220734 prefixEnd_6220734 := by exact prefixLift 6220734
  have htrace : WordTrace (prefixWord ++ tailWord_6220734) baseStart_6220734 baseEnd_6220734 := by
    simpa [prefixWord, tailWord_6220734, baseEnd_6220734] using wordTrace_append hprefix tailTrace_6220734
  have hstable : (prefixWord ++ tailWord_6220734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220734).length < 2 ^ (prefixWord ++ tailWord_6220734).sum := by decide
  have hdescent : baseEnd_6220734 < baseStart_6220734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220744 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 7]
def baseStart_6220744 : Nat := 118140960795 + 6220744 * 2 ^ 59
def prefixEnd_6220744 : Nat := 4983230072969 + 3 ^ 40 * 6220744 * 2
def baseEnd_6220744 : Nat := 354914633396968282687925

theorem tailTrace_6220744 : CollatzResearch.WordTrace tailWord_6220744 prefixEnd_6220744 354914633396968282687925 := by
  unfold tailWord_6220744
  simp only [CollatzResearch.WordTrace]
  refine ⟨113444586687657190668426643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151259448916876254224568857 113444586687657190668426643)
  ·
    refine ⟨170166880031485786002639965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113444586687657190668426643 170166880031485786002639965)
    ·
      refine ⟨63812580011807169750989987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170166880031485786002639965 63812580011807169750989987)
      ·
        refine ⟨95718870017710754626484981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63812580011807169750989987 95718870017710754626484981)
        ·
          refine ⟨8973644064160383246232967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95718870017710754626484981 8973644064160383246232967)
          ·
            refine ⟨13460466096240574869349451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973644064160383246232967 13460466096240574869349451)
            ·
              refine ⟨20190699144360862304024177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460466096240574869349451 20190699144360862304024177)
              ·
                refine ⟨15143024358270646728018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20190699144360862304024177 15143024358270646728018133)
                ·
                  refine ⟨354914633396968282687925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15143024358270646728018133 354914633396968282687925)
                  ·
                    rfl

theorem cell23_6220744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_6220744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220744 prefixEnd_6220744 := by exact prefixLift 6220744
  have htrace : WordTrace (prefixWord ++ tailWord_6220744) baseStart_6220744 baseEnd_6220744 := by
    simpa [prefixWord, tailWord_6220744, baseEnd_6220744] using wordTrace_append hprefix tailTrace_6220744
  have hstable : (prefixWord ++ tailWord_6220744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220744).length < 2 ^ (prefixWord ++ tailWord_6220744).sum := by decide
  have hdescent : baseEnd_6220744 < baseStart_6220744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220761 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 5]
def baseStart_6220761 : Nat := 118140960795 + 6220761 * 2 ^ 59
def prefixEnd_6220761 : Nat := 4983230072969 + 3 ^ 40 * 6220761 * 2
def baseEnd_6220761 : Nat := 354915603304871219742083

theorem tailTrace_6220761 : CollatzResearch.WordTrace tailWord_6220761 prefixEnd_6220761 354915603304871219742083 := by
  unfold tailWord_6220761
  simp only [CollatzResearch.WordTrace]
  refine ⟨226889793416252793240222137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151259862277501862160148091 226889793416252793240222137)
  ·
    refine ⟨170167345062189594930166603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226889793416252793240222137 170167345062189594930166603)
    ·
      refine ⟨255251017593284392395249905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170167345062189594930166603 255251017593284392395249905)
      ·
        refine ⟨191438263194963294296437429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255251017593284392395249905 191438263194963294296437429)
        ·
          refine ⟨17947337174527808840291009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191438263194963294296437429 17947337174527808840291009)
          ·
            refine ⟨13460502880895856630218257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17947337174527808840291009 13460502880895856630218257)
            ·
              refine ⟨10095377160671892472663693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13460502880895856630218257 10095377160671892472663693)
              ·
                refine ⟨3785766435251959677248885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10095377160671892472663693 3785766435251959677248885)
                ·
                  refine ⟨354915603304871219742083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3785766435251959677248885 354915603304871219742083)
                  ·
                    rfl

theorem cell23_6220761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 5].length) (baseStart_6220761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220761 prefixEnd_6220761 := by exact prefixLift 6220761
  have htrace : WordTrace (prefixWord ++ tailWord_6220761) baseStart_6220761 baseEnd_6220761 := by
    simpa [prefixWord, tailWord_6220761, baseEnd_6220761] using wordTrace_append hprefix tailTrace_6220761
  have hstable : (prefixWord ++ tailWord_6220761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220761).length < 2 ^ (prefixWord ++ tailWord_6220761).sum := by decide
  have hdescent : baseEnd_6220761 < baseStart_6220761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220789 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6220789 : Nat := 118140960795 + 6220789 * 2 ^ 59
def prefixEnd_6220789 : Nat := 4983230072969 + 3 ^ 40 * 6220789 * 2
def baseEnd_6220789 : Nat := 3194254807202166868128619

theorem tailTrace_6220789 : CollatzResearch.WordTrace tailWord_6220789 prefixEnd_6220789 3194254807202166868128619 := by
  unfold tailWord_6220789
  simp only [CollatzResearch.WordTrace]
  refine ⟨226890814660151354022241421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151260543106767569348160947 226890814660151354022241421)
  ·
    refine ⟨85084055497556757758340533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226890814660151354022241421 85084055497556757758340533)
    ·
      refine ⟨7976630202895946039844425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85084055497556757758340533 7976630202895946039844425)
      ·
        refine ⟨5982472652171959529883319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7976630202895946039844425 5982472652171959529883319)
        ·
          refine ⟨8973708978257939294824979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5982472652171959529883319 8973708978257939294824979)
          ·
            refine ⟨13460563467386908942237469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973708978257939294824979 13460563467386908942237469)
            ·
              refine ⟨5047711300270090853339051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13460563467386908942237469 5047711300270090853339051)
              ·
                refine ⟨7571566950405136280008577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047711300270090853339051 7571566950405136280008577)
                ·
                  refine ⟨5678675212803852210006433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7571566950405136280008577 5678675212803852210006433)
                  ·
                    refine ⟨4259006409602889157504825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5678675212803852210006433 4259006409602889157504825)
                    ·
                      refine ⟨3194254807202166868128619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259006409602889157504825 3194254807202166868128619)
                      ·
                        rfl

theorem cell23_6220789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6220789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220789 prefixEnd_6220789 := by exact prefixLift 6220789
  have htrace : WordTrace (prefixWord ++ tailWord_6220789) baseStart_6220789 baseEnd_6220789 := by
    simpa [prefixWord, tailWord_6220789, baseEnd_6220789] using wordTrace_append hprefix tailTrace_6220789
  have hstable : (prefixWord ++ tailWord_6220789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220789).length < 2 ^ (prefixWord ++ tailWord_6220789).sum := by decide
  have hdescent : baseEnd_6220789 < baseStart_6220789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220831 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_6220831 : Nat := 118140960795 + 6220831 * 2 ^ 59
def prefixEnd_6220831 : Nat := 4983230072969 + 3 ^ 40 * 6220831 * 2
def baseEnd_6220831 : Nat := 3194276373389655703803425

theorem tailTrace_6220831 : CollatzResearch.WordTrace tailWord_6220831 prefixEnd_6220831 3194276373389655703803425 := by
  unfold tailWord_6220831
  simp only [CollatzResearch.WordTrace]
  refine ⟨226892346525999195195270347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151261564350666130130180231 226892346525999195195270347)
  ·
    refine ⟨340338519788998792792905521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226892346525999195195270347 340338519788998792792905521)
    ·
      refine ⟨255253889841749094594679141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340338519788998792792905521 255253889841749094594679141)
      ·
        refine ⟨47860104345327955236502339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255253889841749094594679141 47860104345327955236502339)
        ·
          refine ⟨71790156517991932854753509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47860104345327955236502339 71790156517991932854753509)
          ·
            refine ⟨13460654347123487410266283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71790156517991932854753509 13460654347123487410266283)
            ·
              refine ⟨20190981520685231115399425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13460654347123487410266283 20190981520685231115399425)
              ·
                refine ⟨15143236140513923336549569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20190981520685231115399425 15143236140513923336549569)
                ·
                  refine ⟨11357427105385442502412177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15143236140513923336549569 11357427105385442502412177)
                  ·
                    refine ⟨8518070329039081876809133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11357427105385442502412177 8518070329039081876809133)
                    ·
                      refine ⟨3194276373389655703803425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8518070329039081876809133 3194276373389655703803425)
                      ·
                        rfl

theorem cell23_6220831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_6220831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220831 prefixEnd_6220831 := by exact prefixLift 6220831
  have htrace : WordTrace (prefixWord ++ tailWord_6220831) baseStart_6220831 baseEnd_6220831 := by
    simpa [prefixWord, tailWord_6220831, baseEnd_6220831] using wordTrace_append hprefix tailTrace_6220831
  have hstable : (prefixWord ++ tailWord_6220831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220831).length < 2 ^ (prefixWord ++ tailWord_6220831).sum := by decide
  have hdescent : baseEnd_6220831 < baseStart_6220831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220834 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_6220834 : Nat := 118140960795 + 6220834 * 2 ^ 59
def prefixEnd_6220834 : Nat := 4983230072969 + 3 ^ 40 * 6220834 * 2
def baseEnd_6220834 : Nat := 354919768203513243562879

theorem tailTrace_6220834 : CollatzResearch.WordTrace tailWord_6220834 prefixEnd_6220834 354919768203513243562879 := by
  unfold tailWord_6220834
  simp only [CollatzResearch.WordTrace]
  refine ⟨56723113986247081676907389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151261637296658884471753037 56723113986247081676907389)
  ·
    refine ⟨21271167744842655628840271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56723113986247081676907389 21271167744842655628840271)
    ·
      refine ⟨31906751617263983443260407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21271167744842655628840271 31906751617263983443260407)
      ·
        refine ⟨47860127425895975164890611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31906751617263983443260407 47860127425895975164890611)
        ·
          refine ⟨71790191138843962747335917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47860127425895975164890611 71790191138843962747335917)
          ·
            refine ⟨26921321677066486030250969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71790191138843962747335917 26921321677066486030250969)
            ·
              refine ⟨20190991257799864522688227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26921321677066486030250969 20190991257799864522688227)
              ·
                refine ⟨30286486886699796784032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20190991257799864522688227 30286486886699796784032341)
                ·
                  refine ⟨354919768203513243562879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30286486886699796784032341 354919768203513243562879)
                  ·
                    rfl

theorem cell23_6220834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_6220834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220834 prefixEnd_6220834 := by exact prefixLift 6220834
  have htrace : WordTrace (prefixWord ++ tailWord_6220834) baseStart_6220834 baseEnd_6220834 := by
    simpa [prefixWord, tailWord_6220834, baseEnd_6220834] using wordTrace_append hprefix tailTrace_6220834
  have hstable : (prefixWord ++ tailWord_6220834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220834).length < 2 ^ (prefixWord ++ tailWord_6220834).sum := by decide
  have hdescent : baseEnd_6220834 < baseStart_6220834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220864 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_6220864 : Nat := 118140960795 + 6220864 * 2 ^ 59
def prefixEnd_6220864 : Nat := 4983230072969 + 3 ^ 40 * 6220864 * 2
def baseEnd_6220864 : Nat := 1064764439417084691563591

theorem tailTrace_6220864 : CollatzResearch.WordTrace tailWord_6220864 prefixEnd_6220864 1064764439417084691563591 := by
  unfold tailWord_6220864
  simp only [CollatzResearch.WordTrace]
  refine ⟨113446775067439820915610823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151262366756586427887481097 113446775067439820915610823)
  ·
    refine ⟨170170162601159731373416235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113446775067439820915610823 170170162601159731373416235)
    ·
      refine ⟨255255243901739597060124353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170170162601159731373416235 255255243901739597060124353)
      ·
        refine ⟨191441432926304697795093265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255255243901739597060124353 191441432926304697795093265)
        ·
          refine ⟨143581074694728523346319949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191441432926304697795093265 143581074694728523346319949)
          ·
            refine ⟨53842903010523196254869981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143581074694728523346319949 53842903010523196254869981)
            ·
              refine ⟨20191088628946198595576243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53842903010523196254869981 20191088628946198595576243)
              ·
                refine ⟨30286632943419297893364365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20191088628946198595576243 30286632943419297893364365)
                ·
                  refine ⟨11357487353782236710011637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30286632943419297893364365 11357487353782236710011637)
                  ·
                    refine ⟨1064764439417084691563591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11357487353782236710011637 1064764439417084691563591)
                    ·
                      rfl

theorem cell23_6220864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_6220864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220864 prefixEnd_6220864 := by exact prefixLift 6220864
  have htrace : WordTrace (prefixWord ++ tailWord_6220864) baseStart_6220864 baseEnd_6220864 := by
    simpa [prefixWord, tailWord_6220864, baseEnd_6220864] using wordTrace_append hprefix tailTrace_6220864
  have hstable : (prefixWord ++ tailWord_6220864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220864).length < 2 ^ (prefixWord ++ tailWord_6220864).sum := by decide
  have hdescent : baseEnd_6220864 < baseStart_6220864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220911 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 2, 4]
def baseStart_6220911 : Nat := 118140960795 + 6220911 * 2 ^ 59
def prefixEnd_6220911 : Nat := 4983230072969 + 3 ^ 40 * 6220911 * 2
def baseEnd_6220911 : Nat := 1064772483947338463601019

theorem tailTrace_6220911 : CollatzResearch.WordTrace tailWord_6220911 prefixEnd_6220911 1064772483947338463601019 := by
  unfold tailWord_6220911
  simp only [CollatzResearch.WordTrace]
  refine ⟨226895264365709368858182587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151263509577139579238788391 226895264365709368858182587)
  ·
    refine ⟨340342896548564053287273881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226895264365709368858182587 340342896548564053287273881)
    ·
      refine ⟨255257172411423039965455411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340342896548564053287273881 255257172411423039965455411)
      ·
        refine ⟨382885758617134559948183117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255257172411423039965455411 382885758617134559948183117)
        ·
          refine ⟨143582159481425459980568669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382885758617134559948183117 143582159481425459980568669)
          ·
            refine ⟨53843309805534547492713251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143582159481425459980568669 53843309805534547492713251)
            ·
              refine ⟨80764964708301821239069877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53843309805534547492713251 80764964708301821239069877)
              ·
                refine ⟨7571715441403295741162801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80764964708301821239069877 7571715441403295741162801)
                ·
                  refine ⟨5678786581052471805872101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7571715441403295741162801 5678786581052471805872101)
                  ·
                    refine ⟨1064772483947338463601019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678786581052471805872101 1064772483947338463601019)
                    ·
                      rfl

theorem cell23_6220911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_6220911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220911 prefixEnd_6220911 := by exact prefixLift 6220911
  have htrace : WordTrace (prefixWord ++ tailWord_6220911) baseStart_6220911 baseEnd_6220911 := by
    simpa [prefixWord, tailWord_6220911, baseEnd_6220911] using wordTrace_append hprefix tailTrace_6220911
  have hstable : (prefixWord ++ tailWord_6220911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220911).length < 2 ^ (prefixWord ++ tailWord_6220911).sum := by decide
  have hdescent : baseEnd_6220911 < baseStart_6220911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220918 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6220918 : Nat := 118140960795 + 6220918 * 2 ^ 59
def prefixEnd_6220918 : Nat := 4983230072969 + 3 ^ 40 * 6220918 * 2
def baseEnd_6220918 : Nat := 3194321046206596863415525

theorem tailTrace_6220918 : CollatzResearch.WordTrace tailWord_6220918 prefixEnd_6220918 3194321046206596863415525 := by
  unfold tailWord_6220918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180969979792750565855463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151263679784456006035791605 14180969979792750565855463)
  ·
    refine ⟨21271454969689125848783195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14180969979792750565855463 21271454969689125848783195)
    ·
      refine ⟨31907182454533688773174793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21271454969689125848783195 31907182454533688773174793)
      ·
        refine ⟨23930386840900266579881095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31907182454533688773174793 23930386840900266579881095)
        ·
          refine ⟨35895580261350399869821643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23930386840900266579881095 35895580261350399869821643)
          ·
            refine ⟨53843370392025599804732465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35895580261350399869821643 53843370392025599804732465)
            ·
              refine ⟨40382527794019199853549349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53843370392025599804732465 40382527794019199853549349)
              ·
                refine ⟨7571723961378599972540503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40382527794019199853549349 7571723961378599972540503)
                ·
                  refine ⟨11357585942067899958810755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571723961378599972540503 11357585942067899958810755)
                  ·
                    refine ⟨17036378913101849938216133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11357585942067899958810755 17036378913101849938216133)
                    ·
                      refine ⟨3194321046206596863415525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17036378913101849938216133 3194321046206596863415525)
                      ·
                        rfl

theorem cell23_6220918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6220918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220918 prefixEnd_6220918 := by exact prefixLift 6220918
  have htrace : WordTrace (prefixWord ++ tailWord_6220918) baseStart_6220918 baseEnd_6220918 := by
    simpa [prefixWord, tailWord_6220918, baseEnd_6220918] using wordTrace_append hprefix tailTrace_6220918
  have hstable : (prefixWord ++ tailWord_6220918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220918).length < 2 ^ (prefixWord ++ tailWord_6220918).sum := by decide
  have hdescent : baseEnd_6220918 < baseStart_6220918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220938 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6220938 : Nat := 118140960795 + 6220938 * 2 ^ 59
def prefixEnd_6220938 : Nat := 4983230072969 + 3 ^ 40 * 6220938 * 2
def baseEnd_6220938 : Nat := 3194331315819686785165433

theorem tailTrace_6220938 : CollatzResearch.WordTrace tailWord_6220938 prefixEnd_6220938 3194331315819686785165433 := by
  unfold tailWord_6220938
  simp only [CollatzResearch.WordTrace]
  refine ⟨56724062284152888117353867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151264166091074368312943645 56724062284152888117353867)
  ·
    refine ⟨85086093426229332176030801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56724062284152888117353867 85086093426229332176030801)
    ·
      refine ⟨63814570069671999132023101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85086093426229332176030801 63814570069671999132023101)
      ·
        refine ⟨23930463776126999674508663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63814570069671999132023101 23930463776126999674508663)
        ·
          refine ⟨35895695664190499511762995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23930463776126999674508663 35895695664190499511762995)
          ·
            refine ⟨53843543496285749267644493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35895695664190499511762995 53843543496285749267644493)
            ·
              refine ⟨20191328811107155975366685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53843543496285749267644493 20191328811107155975366685)
              ·
                refine ⟨7571748304165183490762507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20191328811107155975366685 7571748304165183490762507)
                ·
                  refine ⟨11357622456247775236143761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571748304165183490762507 11357622456247775236143761)
                  ·
                    refine ⟨8518216842185831427107821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11357622456247775236143761 8518216842185831427107821)
                    ·
                      refine ⟨3194331315819686785165433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8518216842185831427107821 3194331315819686785165433)
                      ·
                        rfl

theorem cell23_6220938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6220938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220938 prefixEnd_6220938 := by exact prefixLift 6220938
  have htrace : WordTrace (prefixWord ++ tailWord_6220938) baseStart_6220938 baseEnd_6220938 := by
    simpa [prefixWord, tailWord_6220938, baseEnd_6220938] using wordTrace_append hprefix tailTrace_6220938
  have hstable : (prefixWord ++ tailWord_6220938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220938).length < 2 ^ (prefixWord ++ tailWord_6220938).sum := by decide
  have hdescent : baseEnd_6220938 < baseStart_6220938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220952 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6220952 : Nat := 118140960795 + 6220952 * 2 ^ 59
def prefixEnd_6220952 : Nat := 4983230072969 + 3 ^ 40 * 6220952 * 2
def baseEnd_6220952 : Nat := 3194338504548849730390369

theorem tailTrace_6220952 : CollatzResearch.WordTrace tailWord_6220952 prefixEnd_6220952 3194338504548849730390369 := by
  unfold tailWord_6220952
  simp only [CollatzResearch.WordTrace]
  refine ⟨113448379879280416430212555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151264506505707221906950073 113448379879280416430212555)
  ·
    refine ⟨170172569818920624645318833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113448379879280416430212555 170172569818920624645318833)
    ·
      refine ⟨127629427364190468483989125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170172569818920624645318833 127629427364190468483989125)
      ·
        refine ⟨23930517630785712840747961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127629427364190468483989125 23930517630785712840747961)
        ·
          refine ⟨17947888223089284630560971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23930517630785712840747961 17947888223089284630560971)
          ·
            refine ⟨26921832334633926945841457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17947888223089284630560971 26921832334633926945841457)
            ·
              refine ⟨20191374250975445209381093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26921832334633926945841457 20191374250975445209381093)
              ·
                refine ⟨3785882672057895976758955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20191374250975445209381093 3785882672057895976758955)
                ·
                  refine ⟨5678824008086843965138433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785882672057895976758955 5678824008086843965138433)
                  ·
                    refine ⟨4259118006065132973853825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5678824008086843965138433 4259118006065132973853825)
                    ·
                      refine ⟨3194338504548849730390369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259118006065132973853825 3194338504548849730390369)
                      ·
                        rfl

theorem cell23_6220952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6220952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220952 prefixEnd_6220952 := by exact prefixLift 6220952
  have htrace : WordTrace (prefixWord ++ tailWord_6220952) baseStart_6220952 baseEnd_6220952 := by
    simpa [prefixWord, tailWord_6220952, baseEnd_6220952] using wordTrace_append hprefix tailTrace_6220952
  have hstable : (prefixWord ++ tailWord_6220952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220952).length < 2 ^ (prefixWord ++ tailWord_6220952).sum := by decide
  have hdescent : baseEnd_6220952 < baseStart_6220952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220962 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_6220962 : Nat := 118140960795 + 6220962 * 2 ^ 59
def prefixEnd_6220962 : Nat := 4983230072969 + 3 ^ 40 * 6220962 * 2
def baseEnd_6220962 : Nat := 1064781213118464897088441

theorem tailTrace_6220962 : CollatzResearch.WordTrace tailWord_6220962 prefixEnd_6220962 1064781213118464897088441 := by
  unfold tailWord_6220962
  simp only [CollatzResearch.WordTrace]
  refine ⟨56724281122131151142072285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151264749659016403045526093 56724281122131151142072285)
  ·
    refine ⟨21271605420799181678277107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56724281122131151142072285 21271605420799181678277107)
    ·
      refine ⟨31907408131198772517415661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21271605420799181678277107 31907408131198772517415661)
      ·
        refine ⟨11965278049199539694030873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31907408131198772517415661 11965278049199539694030873)
        ·
          refine ⟨8973958536899654770523155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11965278049199539694030873 8973958536899654770523155)
          ·
            refine ⟨13460937805349482155784733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8973958536899654770523155 13460937805349482155784733)
            ·
              refine ⟨5047851677006055808419275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13460937805349482155784733 5047851677006055808419275)
              ·
                refine ⟨7571777515509083712628913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5047851677006055808419275 7571777515509083712628913)
                ·
                  refine ⟨5678833136631812784471685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7571777515509083712628913 5678833136631812784471685)
                  ·
                    refine ⟨1064781213118464897088441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5678833136631812784471685 1064781213118464897088441)
                    ·
                      rfl

theorem cell23_6220962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_6220962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220962 prefixEnd_6220962 := by exact prefixLift 6220962
  have htrace : WordTrace (prefixWord ++ tailWord_6220962) baseStart_6220962 baseEnd_6220962 := by
    simpa [prefixWord, tailWord_6220962, baseEnd_6220962] using wordTrace_append hprefix tailTrace_6220962
  have hstable : (prefixWord ++ tailWord_6220962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220962).length < 2 ^ (prefixWord ++ tailWord_6220962).sum := by decide
  have hdescent : baseEnd_6220962 < baseStart_6220962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6220984 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_6220984 : Nat := 118140960795 + 6220984 * 2 ^ 59
def prefixEnd_6220984 : Nat := 4983230072969 + 3 ^ 40 * 6220984 * 2
def baseEnd_6220984 : Nat := 1064784978643264535063407

theorem tailTrace_6220984 : CollatzResearch.WordTrace tailWord_6220984 prefixEnd_6220984 1064784978643264535063407 := by
  unfold tailWord_6220984
  simp only [CollatzResearch.WordTrace]
  refine ⟨113448963447222451162795003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151265284596296601550393337 113448963447222451162795003)
  ·
    refine ⟨170173445170833676744192505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113448963447222451162795003 170173445170833676744192505)
    ·
      refine ⟨127630083878125257558144379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170173445170833676744192505 127630083878125257558144379)
      ·
        refine ⟨191445125817187886337216569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127630083878125257558144379 191445125817187886337216569)
        ·
          refine ⟨143583844362890914752912427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191445125817187886337216569 143583844362890914752912427)
          ·
            refine ⟨215375766544336372129368641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143583844362890914752912427 215375766544336372129368641)
            ·
              refine ⟨161531824908252279097026481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215375766544336372129368641 161531824908252279097026481)
              ·
                refine ⟨121148868681189209322769861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161531824908252279097026481 121148868681189209322769861)
                ·
                  refine ⟨22715412877722976748019349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121148868681189209322769861 22715412877722976748019349)
                  ·
                    refine ⟨1064784978643264535063407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22715412877722976748019349 1064784978643264535063407)
                    ·
                      rfl

theorem cell23_6220984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_6220984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6220984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6220984 prefixEnd_6220984 := by exact prefixLift 6220984
  have htrace : WordTrace (prefixWord ++ tailWord_6220984) baseStart_6220984 baseEnd_6220984 := by
    simpa [prefixWord, tailWord_6220984, baseEnd_6220984] using wordTrace_append hprefix tailTrace_6220984
  have hstable : (prefixWord ++ tailWord_6220984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6220984).length < 2 ^ (prefixWord ++ tailWord_6220984).sum := by decide
  have hdescent : baseEnd_6220984 < baseStart_6220984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6220984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221029 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6221029 : Nat := 118140960795 + 6221029 * 2 ^ 59
def prefixEnd_6221029 : Nat := 4983230072969 + 3 ^ 40 * 6221029 * 2
def baseEnd_6221029 : Nat := 3194378042559245929127515

theorem tailTrace_6221029 : CollatzResearch.WordTrace tailWord_6221029 prefixEnd_6221029 3194378042559245929127515 := by
  unfold tailWord_6221029
  simp only [CollatzResearch.WordTrace]
  refine ⟨226899568179281875010978141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151266378786187916673985427 226899568179281875010978141)
  ·
    refine ⟨85087338067230703129116803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226899568179281875010978141 85087338067230703129116803)
    ·
      refine ⟨127631007100846054693675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85087338067230703129116803 127631007100846054693675205)
      ·
        refine ⟨23930813831408635255064101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127631007100846054693675205 23930813831408635255064101)
        ·
          refine ⟨4487027593389119110324519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23930813831408635255064101 4487027593389119110324519)
          ·
            refine ⟨6730541390083678665486779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487027593389119110324519 6730541390083678665486779)
            ·
              refine ⟨10095812085125517998230169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730541390083678665486779 10095812085125517998230169)
              ·
                refine ⟨7571859063844138498672627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10095812085125517998230169 7571859063844138498672627)
                ·
                  refine ⟨11357788595766207748008941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7571859063844138498672627 11357788595766207748008941)
                  ·
                    refine ⟨4259170723412327905503353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11357788595766207748008941 4259170723412327905503353)
                    ·
                      refine ⟨3194378042559245929127515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259170723412327905503353 3194378042559245929127515)
                      ·
                        rfl

theorem cell23_6221029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6221029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221029 prefixEnd_6221029 := by exact prefixLift 6221029
  have htrace : WordTrace (prefixWord ++ tailWord_6221029) baseStart_6221029 baseEnd_6221029 := by
    simpa [prefixWord, tailWord_6221029, baseEnd_6221029] using wordTrace_append hprefix tailTrace_6221029
  have hstable : (prefixWord ++ tailWord_6221029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221029).length < 2 ^ (prefixWord ++ tailWord_6221029).sum := by decide
  have hdescent : baseEnd_6221029 < baseStart_6221029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221041 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_6221041 : Nat := 118140960795 + 6221041 * 2 ^ 59
def prefixEnd_6221041 : Nat := 4983230072969 + 3 ^ 40 * 6221041 * 2
def baseEnd_6221041 : Nat := 3194384204327099882177459

theorem tailTrace_6221041 : CollatzResearch.WordTrace tailWord_6221041 prefixEnd_6221041 3194384204327099882177459 := by
  unfold tailWord_6221041
  simp only [CollatzResearch.WordTrace]
  refine ⟨226900005855238401060414977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151266670570158934040276651 226900005855238401060414977)
  ·
    refine ⟨170175004391428800795311233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226900005855238401060414977 170175004391428800795311233)
    ·
      refine ⟨127631253293571600596483425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170175004391428800795311233 127631253293571600596483425)
      ·
        refine ⟨95723439970178700447362569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127631253293571600596483425 95723439970178700447362569)
        ·
          refine ⟨71792579977634025335521927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95723439970178700447362569 71792579977634025335521927)
          ·
            refine ⟨107688869966451038003282891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71792579977634025335521927 107688869966451038003282891)
            ·
              refine ⟨161533304949676557004924337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107688869966451038003282891 161533304949676557004924337)
              ·
                refine ⟨121149978712257417753693253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161533304949676557004924337 121149978712257417753693253)
                ·
                  refine ⟨22715621008548265828817485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121149978712257417753693253 22715621008548265828817485)
                  ·
                    refine ⟨8518357878205599685806557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22715621008548265828817485 8518357878205599685806557)
                    ·
                      refine ⟨3194384204327099882177459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8518357878205599685806557 3194384204327099882177459)
                      ·
                        rfl

theorem cell23_6221041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_6221041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221041 prefixEnd_6221041 := by exact prefixLift 6221041
  have htrace : WordTrace (prefixWord ++ tailWord_6221041) baseStart_6221041 baseEnd_6221041 := by
    simpa [prefixWord, tailWord_6221041, baseEnd_6221041] using wordTrace_append hprefix tailTrace_6221041
  have hstable : (prefixWord ++ tailWord_6221041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221041).length < 2 ^ (prefixWord ++ tailWord_6221041).sum := by decide
  have hdescent : baseEnd_6221041 < baseStart_6221041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221061 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_6221061 : Nat := 118140960795 + 6221061 * 2 ^ 59
def prefixEnd_6221061 : Nat := 4983230072969 + 3 ^ 40 * 6221061 * 2
def baseEnd_6221061 : Nat := 1064798157980063267975789

theorem tailTrace_6221061 : CollatzResearch.WordTrace tailWord_6221061 prefixEnd_6221061 1064798157980063267975789 := by
  unfold tailWord_6221061
  simp only [CollatzResearch.WordTrace]
  refine ⟨226900735315165944476143037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151267156876777296317428691 226900735315165944476143037)
  ·
    refine ⟨85087775743187229178553639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226900735315165944476143037 85087775743187229178553639)
    ·
      refine ⟨127631663614780843767830459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85087775743187229178553639 127631663614780843767830459)
      ·
        refine ⟨191447495422171265651745689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127631663614780843767830459 191447495422171265651745689)
        ·
          refine ⟨143585621566628449238809267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191447495422171265651745689 143585621566628449238809267)
          ·
            refine ⟨215378432349942673858213901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143585621566628449238809267 215378432349942673858213901)
            ·
              refine ⟨80766912131228502696830213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215378432349942673858213901 80766912131228502696830213)
              ·
                refine ⟨15143796024605344255655665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80766912131228502696830213 15143796024605344255655665)
                ·
                  refine ⟨11357847018454008191741749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15143796024605344255655665 11357847018454008191741749)
                  ·
                    refine ⟨1064798157980063267975789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11357847018454008191741749 1064798157980063267975789)
                    ·
                      rfl

theorem cell23_6221061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_6221061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221061 prefixEnd_6221061 := by exact prefixLift 6221061
  have htrace : WordTrace (prefixWord ++ tailWord_6221061) baseStart_6221061 baseEnd_6221061 := by
    simpa [prefixWord, tailWord_6221061, baseEnd_6221061] using wordTrace_append hprefix tailTrace_6221061
  have hstable : (prefixWord ++ tailWord_6221061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221061).length < 2 ^ (prefixWord ++ tailWord_6221061).sum := by decide
  have hdescent : baseEnd_6221061 < baseStart_6221061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221068 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_6221068 : Nat := 118140960795 + 6221068 * 2 ^ 59
def prefixEnd_6221068 : Nat := 4983230072969 + 3 ^ 40 * 6221068 * 2
def baseEnd_6221068 : Nat := 3194398068304771276539835

theorem tailTrace_6221068 : CollatzResearch.WordTrace tailWord_6221068 prefixEnd_6221068 3194398068304771276539835 := by
  unfold tailWord_6221068
  simp only [CollatzResearch.WordTrace]
  refine ⟨113450495313070292335823929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151267327084093723114431905 113450495313070292335823929)
  ·
    refine ⟨85087871484802719251867947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113450495313070292335823929 85087871484802719251867947)
    ·
      refine ⟨127631807227204078877801921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85087871484802719251867947 127631807227204078877801921)
      ·
        refine ⟨95723855420403059158351441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127631807227204078877801921 95723855420403059158351441)
        ·
          refine ⟨71792891565302294368763581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95723855420403059158351441 71792891565302294368763581)
          ·
            refine ⟨26922334336988360388286343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71792891565302294368763581 26922334336988360388286343)
            ·
              refine ⟨40383501505482540582429515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26922334336988360388286343 40383501505482540582429515)
              ·
                refine ⟨60575252258223810873644273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40383501505482540582429515 60575252258223810873644273)
                ·
                  refine ⟨45431439193667858155233205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60575252258223810873644273 45431439193667858155233205)
                  ·
                    refine ⟨4259197424406361702053113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45431439193667858155233205 4259197424406361702053113)
                    ·
                      refine ⟨3194398068304771276539835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259197424406361702053113 3194398068304771276539835)
                      ·
                        rfl

theorem cell23_6221068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_6221068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221068 prefixEnd_6221068 := by exact prefixLift 6221068
  have htrace : WordTrace (prefixWord ++ tailWord_6221068) baseStart_6221068 baseEnd_6221068 := by
    simpa [prefixWord, tailWord_6221068, baseEnd_6221068] using wordTrace_append hprefix tailTrace_6221068
  have hstable : (prefixWord ++ tailWord_6221068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221068).length < 2 ^ (prefixWord ++ tailWord_6221068).sum := by decide
  have hdescent : baseEnd_6221068 < baseStart_6221068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221159 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 1, 4]
def baseStart_6221159 : Nat := 118140960795 + 6221159 * 2 ^ 59
def prefixEnd_6221159 : Nat := 4983230072969 + 3 ^ 40 * 6221159 * 2
def baseEnd_6221159 : Nat := 1064814931681443473500639

theorem tailTrace_6221159 : CollatzResearch.WordTrace tailWord_6221159 prefixEnd_6221159 1064814931681443473500639 := by
  unfold tailWord_6221159
  simp only [CollatzResearch.WordTrace]
  refine ⟨226904309668810907213210531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151269539779207271475473687 226904309668810907213210531)
  ·
    refine ⟨340356464503216360819815797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226904309668810907213210531 340356464503216360819815797)
    ·
      refine ⟨31908418547176533826857731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340356464503216360819815797 31908418547176533826857731)
      ·
        refine ⟨47862627820764800740286597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31908418547176533826857731 47862627820764800740286597)
        ·
          refine ⟨8974242716393400138803737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47862627820764800740286597 8974242716393400138803737)
          ·
            refine ⟨6730682037295050104102803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8974242716393400138803737 6730682037295050104102803)
            ·
              refine ⟨10096023055942575156154205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730682037295050104102803 10096023055942575156154205)
              ·
                refine ⟨3786008645978465683557827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10096023055942575156154205 3786008645978465683557827)
                ·
                  refine ⟨5679012968967698525336741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786008645978465683557827 5679012968967698525336741)
                  ·
                    refine ⟨1064814931681443473500639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5679012968967698525336741 1064814931681443473500639)
                    ·
                      rfl

theorem cell23_6221159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_6221159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221159 prefixEnd_6221159 := by exact prefixLift 6221159
  have htrace : WordTrace (prefixWord ++ tailWord_6221159) baseStart_6221159 baseEnd_6221159 := by
    simpa [prefixWord, tailWord_6221159, baseEnd_6221159] using wordTrace_append hprefix tailTrace_6221159
  have hstable : (prefixWord ++ tailWord_6221159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221159).length < 2 ^ (prefixWord ++ tailWord_6221159).sum := by decide
  have hdescent : baseEnd_6221159 < baseStart_6221159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221168 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_6221168 : Nat := 118140960795 + 6221168 * 2 ^ 59
def prefixEnd_6221168 : Nat := 4983230072969 + 3 ^ 40 * 6221168 * 2
def baseEnd_6221168 : Nat := 1064816472123406961763125

theorem tailTrace_6221168 : CollatzResearch.WordTrace tailWord_6221168 prefixEnd_6221168 1064816472123406961763125 := by
  unfold tailWord_6221168
  simp only [CollatzResearch.WordTrace]
  refine ⟨113452318962889150875144079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151269758617185534500192105 113452318962889150875144079)
  ·
    refine ⟨170178478444333726312716119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113452318962889150875144079 170178478444333726312716119)
    ·
      refine ⟨255267717666500589469074179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170178478444333726312716119 255267717666500589469074179)
      ·
        refine ⟨382901576499750884203611269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255267717666500589469074179 382901576499750884203611269)
        ·
          refine ⟨71794045593703290788177113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382901576499750884203611269 71794045593703290788177113)
          ·
            refine ⟨53845534195277468091132835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71794045593703290788177113 53845534195277468091132835)
            ·
              refine ⟨80768301292916202136699253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53845534195277468091132835 80768301292916202136699253)
              ·
                refine ⟨7572028246210893950315555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80768301292916202136699253 7572028246210893950315555)
                ·
                  refine ⟨11358042369316340925473333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572028246210893950315555 11358042369316340925473333)
                  ·
                    refine ⟨1064816472123406961763125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11358042369316340925473333 1064816472123406961763125)
                    ·
                      rfl

theorem cell23_6221168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_6221168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221168 prefixEnd_6221168 := by exact prefixLift 6221168
  have htrace : WordTrace (prefixWord ++ tailWord_6221168) baseStart_6221168 baseEnd_6221168 := by
    simpa [prefixWord, tailWord_6221168, baseEnd_6221168] using wordTrace_append hprefix tailTrace_6221168
  have hstable : (prefixWord ++ tailWord_6221168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221168).length < 2 ^ (prefixWord ++ tailWord_6221168).sum := by decide
  have hdescent : baseEnd_6221168 < baseStart_6221168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221175 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_6221175 : Nat := 118140960795 + 6221175 * 2 ^ 59
def prefixEnd_6221175 : Nat := 4983230072969 + 3 ^ 40 * 6221175 * 2
def baseEnd_6221175 : Nat := 3194453010734802357901843

theorem tailTrace_6221175 : CollatzResearch.WordTrace tailWord_6221175 prefixEnd_6221175 3194453010734802357901843 := by
  unfold tailWord_6221175
  simp only [CollatzResearch.WordTrace]
  refine ⟨226904893236752941945792979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151269928824501961297195319 226904893236752941945792979)
  ·
    refine ⟨340357339855129412918689469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226904893236752941945792979 340357339855129412918689469)
    ·
      refine ⟨127634002445673529844508551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340357339855129412918689469 127634002445673529844508551)
      ·
        refine ⟨191451003668510294766762827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127634002445673529844508551 191451003668510294766762827)
        ·
          refine ⟨287176505502765442150144241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191451003668510294766762827 287176505502765442150144241)
          ·
            refine ⟨215382379127074081612608181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287176505502765442150144241 215382379127074081612608181)
            ·
              refine ⟨20192098043163195151182017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215382379127074081612608181 20192098043163195151182017)
              ·
                refine ⟨15144073532372396363386513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20192098043163195151182017 15144073532372396363386513)
                ·
                  refine ⟨11358055149279297272539885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15144073532372396363386513 11358055149279297272539885)
                  ·
                    refine ⟨4259270680979736477202457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11358055149279297272539885 4259270680979736477202457)
                    ·
                      refine ⟨3194453010734802357901843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259270680979736477202457 3194453010734802357901843)
                      ·
                        rfl

theorem cell23_6221175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_6221175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221175 prefixEnd_6221175 := by exact prefixLift 6221175
  have htrace : WordTrace (prefixWord ++ tailWord_6221175) baseStart_6221175 baseEnd_6221175 := by
    simpa [prefixWord, tailWord_6221175, baseEnd_6221175] using wordTrace_append hprefix tailTrace_6221175
  have hstable : (prefixWord ++ tailWord_6221175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221175).length < 2 ^ (prefixWord ++ tailWord_6221175).sum := by decide
  have hdescent : baseEnd_6221175 < baseStart_6221175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221202 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_6221202 : Nat := 118140960795 + 6221202 * 2 ^ 59
def prefixEnd_6221202 : Nat := 4983230072969 + 3 ^ 40 * 6221202 * 2
def baseEnd_6221202 : Nat := 1064822291570824584088073

theorem tailTrace_6221202 : CollatzResearch.WordTrace tailWord_6221202 prefixEnd_6221202 1064822291570824584088073 := by
  unfold tailWord_6221202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56726469501913781389256465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151270585338436750371350573 56726469501913781389256465)
  ·
    refine ⟨42544852126435336041942349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56726469501913781389256465 42544852126435336041942349)
    ·
      refine ⟨15954319547413251015728381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42544852126435336041942349 15954319547413251015728381)
      ·
        refine ⟨5982869830279969130898143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15954319547413251015728381 5982869830279969130898143)
        ·
          refine ⟨8974304745419953696347215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5982869830279969130898143 8974304745419953696347215)
          ·
            refine ⟨13461457118129930544520823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8974304745419953696347215 13461457118129930544520823)
            ·
              refine ⟨20192185677194895816781235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13461457118129930544520823 20192185677194895816781235)
              ·
                refine ⟨30288278515792343725171853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20192185677194895816781235 30288278515792343725171853)
                ·
                  refine ⟨11358104443422128896939445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30288278515792343725171853 11358104443422128896939445)
                  ·
                    refine ⟨1064822291570824584088073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11358104443422128896939445 1064822291570824584088073)
                    ·
                      rfl

theorem cell23_6221202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_6221202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221202 prefixEnd_6221202 := by exact prefixLift 6221202
  have htrace : WordTrace (prefixWord ++ tailWord_6221202) baseStart_6221202 baseEnd_6221202 := by
    simpa [prefixWord, tailWord_6221202, baseEnd_6221202] using wordTrace_append hprefix tailTrace_6221202
  have hstable : (prefixWord ++ tailWord_6221202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221202).length < 2 ^ (prefixWord ++ tailWord_6221202).sum := by decide
  have hdescent : baseEnd_6221202 < baseStart_6221202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221205 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_6221205 : Nat := 118140960795 + 6221205 * 2 ^ 59
def prefixEnd_6221205 : Nat := 4983230072969 + 3 ^ 40 * 6221205 * 2
def baseEnd_6221205 : Nat := 3194468415154437240526705

theorem tailTrace_6221205 : CollatzResearch.WordTrace tailWord_6221205 prefixEnd_6221205 3194468415154437240526705 := by
  unfold tailWord_6221205
  simp only [CollatzResearch.WordTrace]
  refine ⟨226905987426644257069385069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151270658284429504712923379 226905987426644257069385069)
  ·
    refine ⟨85089745284991596401019401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226905987426644257069385069 85089745284991596401019401)
    ·
      refine ⟨63817308963743697300764551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85089745284991596401019401 63817308963743697300764551)
      ·
        refine ⟨95725963445615545951146827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63817308963743697300764551 95725963445615545951146827)
        ·
          refine ⟨143588945168423318926720241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95725963445615545951146827 143588945168423318926720241)
          ·
            refine ⟨107691708876317489195040181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143588945168423318926720241 107691708876317489195040181)
            ·
              refine ⟨10096097707154764612035017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107691708876317489195040181 10096097707154764612035017)
              ·
                refine ⟨7572073280366073459026263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10096097707154764612035017 7572073280366073459026263)
                ·
                  refine ⟨11358109920549110188539395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572073280366073459026263 11358109920549110188539395)
                  ·
                    refine ⟨17037164880823665282809093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11358109920549110188539395 17037164880823665282809093)
                    ·
                      refine ⟨3194468415154437240526705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17037164880823665282809093 3194468415154437240526705)
                      ·
                        rfl

theorem cell23_6221205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_6221205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221205 prefixEnd_6221205 := by exact prefixLift 6221205
  have htrace : WordTrace (prefixWord ++ tailWord_6221205) baseStart_6221205 baseEnd_6221205 := by
    simpa [prefixWord, tailWord_6221205, baseEnd_6221205] using wordTrace_append hprefix tailTrace_6221205
  have hstable : (prefixWord ++ tailWord_6221205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221205).length < 2 ^ (prefixWord ++ tailWord_6221205).sum := by decide
  have hdescent : baseEnd_6221205 < baseStart_6221205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221239 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 2]
def baseStart_6221239 : Nat := 118140960795 + 6221239 * 2 ^ 59
def prefixEnd_6221239 : Nat := 4983230072969 + 3 ^ 40 * 6221239 * 2
def baseEnd_6221239 : Nat := 3194485873496690107501549

theorem tailTrace_6221239 : CollatzResearch.WordTrace tailWord_6221239 prefixEnd_6221239 3194485873496690107501549 := by
  unfold tailWord_6221239
  simp only [CollatzResearch.WordTrace]
  refine ⟨226907227508521080876122771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151271485005680720584081847 226907227508521080876122771)
  ·
    refine ⟨340360841262781621314184157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226907227508521080876122771 340360841262781621314184157)
    ·
      refine ⟨127635315473543107992819059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340360841262781621314184157 127635315473543107992819059)
      ·
        refine ⟨191452973210314661989228589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127635315473543107992819059 191452973210314661989228589)
        ·
          refine ⟨71794864953867998245960721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191452973210314661989228589 71794864953867998245960721)
          ·
            refine ⟨53846148715400998684470541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71794864953867998245960721 53846148715400998684470541)
            ·
              refine ⟨20192305768275374506676453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53846148715400998684470541 20192305768275374506676453)
              ·
                refine ⟨3786057331551632720001835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20192305768275374506676453 3786057331551632720001835)
                ·
                  refine ⟨5679085997327449080002753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786057331551632720001835 5679085997327449080002753)
                  ·
                    refine ⟨4259314497995586810002065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679085997327449080002753 4259314497995586810002065)
                    ·
                      refine ⟨3194485873496690107501549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259314497995586810002065 3194485873496690107501549)
                      ·
                        rfl

theorem cell23_6221239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_6221239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221239 prefixEnd_6221239 := by exact prefixLift 6221239
  have htrace : WordTrace (prefixWord ++ tailWord_6221239) baseStart_6221239 baseEnd_6221239 := by
    simpa [prefixWord, tailWord_6221239, baseEnd_6221239] using wordTrace_append hprefix tailTrace_6221239
  have hstable : (prefixWord ++ tailWord_6221239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221239).length < 2 ^ (prefixWord ++ tailWord_6221239).sum := by decide
  have hdescent : baseEnd_6221239 < baseStart_6221239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221252 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6221252 : Nat := 118140960795 + 6221252 * 2 ^ 59
def prefixEnd_6221252 : Nat := 4983230072969 + 3 ^ 40 * 6221252 * 2
def baseEnd_6221252 : Nat := 3194492548745198556638989

theorem tailTrace_6221252 : CollatzResearch.WordTrace tailWord_6221252 prefixEnd_6221252 3194492548745198556638989 := by
  unfold tailWord_6221252
  simp only [CollatzResearch.WordTrace]
  refine ⟨113453850828736992048173005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151271801104982656064230673 113453850828736992048173005)
  ·
    refine ⟨42545194060776372018064877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113453850828736992048173005 42545194060776372018064877)
    ·
      refine ⟨15954447772791139506774329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42545194060776372018064877 15954447772791139506774329)
      ·
        refine ⟨11965835829593354630080747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15954447772791139506774329 11965835829593354630080747)
        ·
          refine ⟨17948753744390031945121121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11965835829593354630080747 17948753744390031945121121)
          ·
            refine ⟨13461565308292523958840841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17948753744390031945121121 13461565308292523958840841)
            ·
              refine ⟨10096173981219392969130631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13461565308292523958840841 10096173981219392969130631)
              ·
                refine ⟨15144260971829089453695947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096173981219392969130631 15144260971829089453695947)
                ·
                  refine ⟨22716391457743634180543921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15144260971829089453695947 22716391457743634180543921)
                  ·
                    refine ⟨17037293593307725635407941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22716391457743634180543921 17037293593307725635407941)
                    ·
                      refine ⟨3194492548745198556638989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17037293593307725635407941 3194492548745198556638989)
                      ·
                        rfl

theorem cell23_6221252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6221252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221252 prefixEnd_6221252 := by exact prefixLift 6221252
  have htrace : WordTrace (prefixWord ++ tailWord_6221252) baseStart_6221252 baseEnd_6221252 := by
    simpa [prefixWord, tailWord_6221252, baseEnd_6221252] using wordTrace_append hprefix tailTrace_6221252
  have hstable : (prefixWord ++ tailWord_6221252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221252).length < 2 ^ (prefixWord ++ tailWord_6221252).sum := by decide
  have hdescent : baseEnd_6221252 < baseStart_6221252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221255 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_6221255 : Nat := 118140960795 + 6221255 * 2 ^ 59
def prefixEnd_6221255 : Nat := 4983230072969 + 3 ^ 40 * 6221255 * 2
def baseEnd_6221255 : Nat := 3194494089187162044901475

theorem tailTrace_6221255 : CollatzResearch.WordTrace tailWord_6221255 prefixEnd_6221255 3194494089187162044901475 := by
  unfold tailWord_6221255
  simp only [CollatzResearch.WordTrace]
  refine ⟨226907811076463115608705219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151271874050975410405803479 226907811076463115608705219)
  ·
    refine ⟨340361716614694673413057829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226907811076463115608705219 340361716614694673413057829)
    ·
      refine ⟨63817821865255251264948343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340361716614694673413057829 63817821865255251264948343)
      ·
        refine ⟨95726732797882876897422515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63817821865255251264948343 95726732797882876897422515)
        ·
          refine ⟨143590099196824315346133773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95726732797882876897422515 143590099196824315346133773)
          ·
            refine ⟨53846287198809118254800165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143590099196824315346133773 53846287198809118254800165)
            ·
              refine ⟨10096178849776709672775031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53846287198809118254800165 10096178849776709672775031)
              ·
                refine ⟨15144268274665064509162547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096178849776709672775031 15144268274665064509162547)
                ·
                  refine ⟨22716402411997596763743821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15144268274665064509162547 22716402411997596763743821)
                  ·
                    refine ⟨8518650904499098786403933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22716402411997596763743821 8518650904499098786403933)
                    ·
                      refine ⟨3194494089187162044901475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8518650904499098786403933 3194494089187162044901475)
                      ·
                        rfl

theorem cell23_6221255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_6221255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221255 prefixEnd_6221255 := by exact prefixLift 6221255
  have htrace : WordTrace (prefixWord ++ tailWord_6221255) baseStart_6221255 baseEnd_6221255 := by
    simpa [prefixWord, tailWord_6221255, baseEnd_6221255] using wordTrace_append hprefix tailTrace_6221255
  have hstable : (prefixWord ++ tailWord_6221255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221255).length < 2 ^ (prefixWord ++ tailWord_6221255).sum := by decide
  have hdescent : baseEnd_6221255 < baseStart_6221255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221288 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6221288 : Nat := 118140960795 + 6221288 * 2 ^ 59
def prefixEnd_6221288 : Nat := 4983230072969 + 3 ^ 40 * 6221288 * 2
def baseEnd_6221288 : Nat := 1064837011349586805262941

theorem tailTrace_6221288 : CollatzResearch.WordTrace tailWord_6221288 prefixEnd_6221288 1064837011349586805262941 := by
  unfold tailWord_6221288
  simp only [CollatzResearch.WordTrace]
  refine ⟨113454507342671781122328259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151272676456895708163104345 113454507342671781122328259)
  ·
    refine ⟨170181761014007671683492389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113454507342671781122328259 170181761014007671683492389)
    ·
      refine ⟨31909080190126438440654823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170181761014007671683492389 31909080190126438440654823)
      ·
        refine ⟨47863620285189657660982235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31909080190126438440654823 47863620285189657660982235)
        ·
          refine ⟨71795430427784486491473353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47863620285189657660982235 71795430427784486491473353)
          ·
            refine ⟨53846572820838364868605015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71795430427784486491473353 53846572820838364868605015)
            ·
              refine ⟨80769859231257547302907523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53846572820838364868605015 80769859231257547302907523)
              ·
                refine ⟨121154788846886320954361285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80769859231257547302907523 121154788846886320954361285)
                ·
                  refine ⟨22716522908791185178942741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121154788846886320954361285 22716522908791185178942741)
                  ·
                    refine ⟨1064837011349586805262941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22716522908791185178942741 1064837011349586805262941)
                    ·
                      rfl

theorem cell23_6221288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6221288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221288 prefixEnd_6221288 := by exact prefixLift 6221288
  have htrace : WordTrace (prefixWord ++ tailWord_6221288) baseStart_6221288 baseEnd_6221288 := by
    simpa [prefixWord, tailWord_6221288, baseEnd_6221288] using wordTrace_append hprefix tailTrace_6221288
  have hstable : (prefixWord ++ tailWord_6221288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221288).length < 2 ^ (prefixWord ++ tailWord_6221288).sum := by decide
  have hdescent : baseEnd_6221288 < baseStart_6221288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221295 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 3, 4, 2]
def baseStart_6221295 : Nat := 118140960795 + 6221295 * 2 ^ 59
def prefixEnd_6221295 : Nat := 4983230072969 + 3 ^ 40 * 6221295 * 2
def baseEnd_6221295 : Nat := 3194514628413341888401291

theorem tailTrace_6221295 : CollatzResearch.WordTrace tailWord_6221295 prefixEnd_6221295 3194514628413341888401291 := by
  unfold tailWord_6221295
  simp only [CollatzResearch.WordTrace]
  refine ⟨226909269996318202440161339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151272846664212134960107559 226909269996318202440161339)
  ·
    refine ⟨340363904994477303660242009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226909269996318202440161339 340363904994477303660242009)
    ·
      refine ⟨255272928745857977745181507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340363904994477303660242009 255272928745857977745181507)
      ·
        refine ⟨382909393118786966617772261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255272928745857977745181507 382909393118786966617772261)
        ·
          refine ⟨71795511209772556240832299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382909393118786966617772261 71795511209772556240832299)
          ·
            refine ⟨107693266814658834361248449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71795511209772556240832299 107693266814658834361248449)
            ·
              refine ⟨80769950110994125770936337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107693266814658834361248449 80769950110994125770936337)
              ·
                refine ⟨60577462583245594328202253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80769950110994125770936337 60577462583245594328202253)
                ·
                  refine ⟨22716548468717097873075845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60577462583245594328202253 22716548468717097873075845)
                  ·
                    refine ⟨4259352837884455851201721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22716548468717097873075845 4259352837884455851201721)
                    ·
                      refine ⟨3194514628413341888401291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259352837884455851201721 3194514628413341888401291)
                      ·
                        rfl

theorem cell23_6221295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4, 2].length) (baseStart_6221295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221295 prefixEnd_6221295 := by exact prefixLift 6221295
  have htrace : WordTrace (prefixWord ++ tailWord_6221295) baseStart_6221295 baseEnd_6221295 := by
    simpa [prefixWord, tailWord_6221295, baseEnd_6221295] using wordTrace_append hprefix tailTrace_6221295
  have hstable : (prefixWord ++ tailWord_6221295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221295).length < 2 ^ (prefixWord ++ tailWord_6221295).sum := by decide
  have hdescent : baseEnd_6221295 < baseStart_6221295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221316 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6221316 : Nat := 118140960795 + 6221316 * 2 ^ 59
def prefixEnd_6221316 : Nat := 4983230072969 + 3 ^ 40 * 6221316 * 2
def baseEnd_6221316 : Nat := 3194525411507086306238695

theorem tailTrace_6221316 : CollatzResearch.WordTrace tailWord_6221316 prefixEnd_6221316 3194525411507086306238695 := by
  unfold tailWord_6221316
  simp only [CollatzResearch.WordTrace]
  refine ⟨113455017964621061513337901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151273357286161415351117201 113455017964621061513337901)
  ·
    refine ⟨42545631736732898067501713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113455017964621061513337901 42545631736732898067501713)
    ·
      refine ⟨31909223802549673550626285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42545631736732898067501713 31909223802549673550626285)
      ·
        refine ⟨11965958925956127581484857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31909223802549673550626285 11965958925956127581484857)
        ·
          refine ⟨8974469194467095686113643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11965958925956127581484857 8974469194467095686113643)
          ·
            refine ⟨13461703791700643529170465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8974469194467095686113643 13461703791700643529170465)
            ·
              refine ⟨10096277843775482646877849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13461703791700643529170465 10096277843775482646877849)
              ·
                refine ⟨7572208382831611985158387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10096277843775482646877849 7572208382831611985158387)
                ·
                  refine ⟨11358312574247417977737581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572208382831611985158387 11358312574247417977737581)
                  ·
                    refine ⟨4259367215342781741651593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11358312574247417977737581 4259367215342781741651593)
                    ·
                      refine ⟨3194525411507086306238695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259367215342781741651593 3194525411507086306238695)
                      ·
                        rfl

theorem cell23_6221316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6221316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221316 prefixEnd_6221316 := by exact prefixLift 6221316
  have htrace : WordTrace (prefixWord ++ tailWord_6221316) baseStart_6221316 baseEnd_6221316 := by
    simpa [prefixWord, tailWord_6221316, baseEnd_6221316] using wordTrace_append hprefix tailTrace_6221316
  have hstable : (prefixWord ++ tailWord_6221316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221316).length < 2 ^ (prefixWord ++ tailWord_6221316).sum := by decide
  have hdescent : baseEnd_6221316 < baseStart_6221316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221429 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6221429 : Nat := 118140960795 + 6221429 * 2 ^ 59
def prefixEnd_6221429 : Nat := 4983230072969 + 3 ^ 40 * 6221429 * 2
def baseEnd_6221429 : Nat := 1064861144940348121375225

theorem tailTrace_6221429 : CollatzResearch.WordTrace tailWord_6221429 prefixEnd_6221429 1064861144940348121375225 := by
  unfold tailWord_6221429
  simp only [CollatzResearch.WordTrace]
  refine ⟨226914157377832743325539341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151276104918555162217026227 226914157377832743325539341)
  ·
    refine ⟨85092809016687278747077253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226914157377832743325539341 85092809016687278747077253)
    ·
      refine ⟨15954901690628864765076985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85092809016687278747077253 15954901690628864765076985)
      ·
        refine ⟨11966176267971648573807739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15954901690628864765076985 11966176267971648573807739)
        ·
          refine ⟨17949264401957472860711609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966176267971648573807739 17949264401957472860711609)
          ·
            refine ⟨13461948301468104645533707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17949264401957472860711609 13461948301468104645533707)
            ·
              refine ⟨20192922452202156968300561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13461948301468104645533707 20192922452202156968300561)
              ·
                refine ⟨15144691839151617726225421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20192922452202156968300561 15144691839151617726225421)
                ·
                  refine ⟨5679259439681856647334533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15144691839151617726225421 5679259439681856647334533)
                  ·
                    refine ⟨1064861144940348121375225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5679259439681856647334533 1064861144940348121375225)
                    ·
                      rfl

theorem cell23_6221429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6221429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221429 prefixEnd_6221429 := by exact prefixLift 6221429
  have htrace : WordTrace (prefixWord ++ tailWord_6221429) baseStart_6221429 baseEnd_6221429 := by
    simpa [prefixWord, tailWord_6221429, baseEnd_6221429] using wordTrace_append hprefix tailTrace_6221429
  have hstable : (prefixWord ++ tailWord_6221429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221429).length < 2 ^ (prefixWord ++ tailWord_6221429).sum := by decide
  have hdescent : baseEnd_6221429 < baseStart_6221429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221452 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_6221452 : Nat := 118140960795 + 6221452 * 2 ^ 59
def prefixEnd_6221452 : Nat := 4983230072969 + 3 ^ 40 * 6221452 * 2
def baseEnd_6221452 : Nat := 3194595244876097774138069

theorem tailTrace_6221452 : CollatzResearch.WordTrace tailWord_6221452 prefixEnd_6221452 3194595244876097774138069 := by
  unfold tailWord_6221452
  simp only [CollatzResearch.WordTrace]
  refine ⟨113457498128374709126813305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151276664171166278835751073 113457498128374709126813305)
  ·
    refine ⟨85093123596281031845109979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113457498128374709126813305 85093123596281031845109979)
    ·
      refine ⟨127639685394421547767664969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85093123596281031845109979 127639685394421547767664969)
      ·
        refine ⟨95729764045816160825748727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127639685394421547767664969 95729764045816160825748727)
        ·
          refine ⟨143594646068724241238623091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95729764045816160825748727 143594646068724241238623091)
          ·
            refine ⟨215391969103086361857934637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143594646068724241238623091 215391969103086361857934637)
            ·
              refine ⟨80771988413657385696725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215391969103086361857934637 80771988413657385696725489)
              ·
                refine ⟨60578991310243039272544117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80771988413657385696725489 60578991310243039272544117)
                ·
                  refine ⟨5679280435335284931801011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60578991310243039272544117 5679280435335284931801011)
                  ·
                    refine ⟨8518920653002927397701517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5679280435335284931801011 8518920653002927397701517)
                    ·
                      refine ⟨3194595244876097774138069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8518920653002927397701517 3194595244876097774138069)
                      ·
                        rfl

theorem cell23_6221452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_6221452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221452 prefixEnd_6221452 := by exact prefixLift 6221452
  have htrace : WordTrace (prefixWord ++ tailWord_6221452) baseStart_6221452 baseEnd_6221452 := by
    simpa [prefixWord, tailWord_6221452, baseEnd_6221452] using wordTrace_append hprefix tailTrace_6221452
  have hstable : (prefixWord ++ tailWord_6221452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221452).length < 2 ^ (prefixWord ++ tailWord_6221452).sum := by decide
  have hdescent : baseEnd_6221452 < baseStart_6221452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221512 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_6221512 : Nat := 118140960795 + 6221512 * 2 ^ 59
def prefixEnd_6221512 : Nat := 4983230072969 + 3 ^ 40 * 6221512 * 2
def baseEnd_6221512 : Nat := 3194626053715367539387793

theorem tailTrace_6221512 : CollatzResearch.WordTrace tailWord_6221512 prefixEnd_6221512 3194626053715367539387793 := by
  unfold tailWord_6221512
  simp only [CollatzResearch.WordTrace]
  refine ⟨113458592318266024250405395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151278123091021365667207193 113458592318266024250405395)
  ·
    refine ⟨170187888477399036375608093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113458592318266024250405395 170187888477399036375608093)
    ·
      refine ⟨63820458179024638640853035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170187888477399036375608093 63820458179024638640853035)
      ·
        refine ⟨95730687268536957961279553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63820458179024638640853035 95730687268536957961279553)
        ·
          refine ⟨71798015451402718470959665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95730687268536957961279553 71798015451402718470959665)
          ·
            refine ⟨53848511588552038853219749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71798015451402718470959665 53848511588552038853219749)
            ·
              refine ⟨10096595922853507284978703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53848511588552038853219749 10096595922853507284978703)
              ·
                refine ⟨15144893884280260927468055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10096595922853507284978703 15144893884280260927468055)
                ·
                  refine ⟨22717340826420391391202083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15144893884280260927468055 22717340826420391391202083)
                  ·
                    refine ⟨34076011239630587086803125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22717340826420391391202083 34076011239630587086803125)
                    ·
                      refine ⟨3194626053715367539387793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34076011239630587086803125 3194626053715367539387793)
                      ·
                        rfl

theorem cell23_6221512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_6221512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221512 prefixEnd_6221512 := by exact prefixLift 6221512
  have htrace : WordTrace (prefixWord ++ tailWord_6221512) baseStart_6221512 baseEnd_6221512 := by
    simpa [prefixWord, tailWord_6221512, baseEnd_6221512] using wordTrace_append hprefix tailTrace_6221512
  have hstable : (prefixWord ++ tailWord_6221512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221512).length < 2 ^ (prefixWord ++ tailWord_6221512).sum := by decide
  have hdescent : baseEnd_6221512 < baseStart_6221512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221522 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6221522 : Nat := 118140960795 + 6221522 * 2 ^ 59
def prefixEnd_6221522 : Nat := 4983230072969 + 3 ^ 40 * 6221522 * 2
def baseEnd_6221522 : Nat := 3194631188521912500262747

theorem tailTrace_6221522 : CollatzResearch.WordTrace tailWord_6221522 prefixEnd_6221522 3194631188521912500262747 := by
  unfold tailWord_6221522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56729387341623955052168705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151278366244330546805783213 56729387341623955052168705)
  ·
    refine ⟨42547040506217966289126529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56729387341623955052168705 42547040506217966289126529)
    ·
      refine ⟨31910280379663474716844897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42547040506217966289126529 31910280379663474716844897)
      ·
        refine ⟨23932710284747606037633673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31910280379663474716844897 23932710284747606037633673)
        ·
          refine ⟨17949532713560704528225255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23932710284747606037633673 17949532713560704528225255)
          ·
            refine ⟨26924299070341056792337883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949532713560704528225255 26924299070341056792337883)
            ·
              refine ⟨40386448605511585188506825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26924299070341056792337883 40386448605511585188506825)
              ·
                refine ⟨30289836454133688891380119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40386448605511585188506825 30289836454133688891380119)
                ·
                  refine ⟨45434754681200533337070179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30289836454133688891380119 45434754681200533337070179)
                  ·
                    refine ⟨68152132021800800005605269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45434754681200533337070179 68152132021800800005605269)
                    ·
                      refine ⟨3194631188521912500262747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68152132021800800005605269 3194631188521912500262747)
                      ·
                        rfl

theorem cell23_6221522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6221522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221522 prefixEnd_6221522 := by exact prefixLift 6221522
  have htrace : WordTrace (prefixWord ++ tailWord_6221522) baseStart_6221522 baseEnd_6221522 := by
    simpa [prefixWord, tailWord_6221522, baseEnd_6221522] using wordTrace_append hprefix tailTrace_6221522
  have hstable : (prefixWord ++ tailWord_6221522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221522).length < 2 ^ (prefixWord ++ tailWord_6221522).sum := by decide
  have hdescent : baseEnd_6221522 < baseStart_6221522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221535 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_6221535 : Nat := 118140960795 + 6221535 * 2 ^ 59
def prefixEnd_6221535 : Nat := 4983230072969 + 3 ^ 40 * 6221535 * 2
def baseEnd_6221535 : Nat := 3194637863770420949400187

theorem tailTrace_6221535 : CollatzResearch.WordTrace tailWord_6221535 prefixEnd_6221535 3194637863770420949400187 := by
  unfold tailWord_6221535
  simp only [CollatzResearch.WordTrace]
  refine ⟨226918023515448723428898059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151278682343632482285932039 226918023515448723428898059)
  ·
    refine ⟨340377035273173085143347089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226918023515448723428898059 340377035273173085143347089)
    ·
      refine ⟨255282776454879813857510317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340377035273173085143347089 255282776454879813857510317)
      ·
        refine ⟨95731041170579930196566369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255282776454879813857510317 95731041170579930196566369)
        ·
          refine ⟨71798280877934947647424777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95731041170579930196566369 71798280877934947647424777)
          ·
            refine ⟨53848710658451210735568583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71798280877934947647424777 53848710658451210735568583)
            ·
              refine ⟨80773065987676816103352875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53848710658451210735568583 80773065987676816103352875)
              ·
                refine ⟨121159598981515224155029313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80773065987676816103352875 121159598981515224155029313)
                ·
                  refine ⟨90869699236136418116271985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121159598981515224155029313 90869699236136418116271985)
                  ·
                    refine ⟨68152274427102313587203989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90869699236136418116271985 68152274427102313587203989)
                    ·
                      refine ⟨3194637863770420949400187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68152274427102313587203989 3194637863770420949400187)
                      ·
                        rfl

theorem cell23_6221535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_6221535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221535 prefixEnd_6221535 := by exact prefixLift 6221535
  have htrace : WordTrace (prefixWord ++ tailWord_6221535) baseStart_6221535 baseEnd_6221535 := by
    simpa [prefixWord, tailWord_6221535, baseEnd_6221535] using wordTrace_append hprefix tailTrace_6221535
  have hstable : (prefixWord ++ tailWord_6221535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221535).length < 2 ^ (prefixWord ++ tailWord_6221535).sum := by decide
  have hdescent : baseEnd_6221535 < baseStart_6221535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221543 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6221543 : Nat := 118140960795 + 6221543 * 2 ^ 59
def prefixEnd_6221543 : Nat := 4983230072969 + 3 ^ 40 * 6221543 * 2
def baseEnd_6221543 : Nat := 3194641971615656918100151

theorem tailTrace_6221543 : CollatzResearch.WordTrace tailWord_6221543 prefixEnd_6221543 3194641971615656918100151 := by
  unfold tailWord_6221543
  simp only [CollatzResearch.WordTrace]
  refine ⟨226918315299419740795189283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151278876866279827196792855 226918315299419740795189283)
  ·
    refine ⟨340377472949129611192783925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226918315299419740795189283 340377472949129611192783925)
    ·
      refine ⟨31910388088980901049323493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340377472949129611192783925 31910388088980901049323493)
      ·
        refine ⟨5983197766683918946748155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31910388088980901049323493 5983197766683918946748155)
        ·
          refine ⟨8974796650025878420122233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983197766683918946748155 8974796650025878420122233)
          ·
            refine ⟨6731097487519408815091675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8974796650025878420122233 6731097487519408815091675)
            ·
              refine ⟨10096646231279113222637513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731097487519408815091675 10096646231279113222637513)
              ·
                refine ⟨7572484673459334916978135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10096646231279113222637513 7572484673459334916978135)
                ·
                  refine ⟨11358727010189002375467203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572484673459334916978135 11358727010189002375467203)
                  ·
                    refine ⟨17038090515283503563200805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11358727010189002375467203 17038090515283503563200805)
                    ·
                      refine ⟨3194641971615656918100151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17038090515283503563200805 3194641971615656918100151)
                      ·
                        rfl

theorem cell23_6221543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6221543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221543 prefixEnd_6221543 := by exact prefixLift 6221543
  have htrace : WordTrace (prefixWord ++ tailWord_6221543) baseStart_6221543 baseEnd_6221543 := by
    simpa [prefixWord, tailWord_6221543, baseEnd_6221543] using wordTrace_append hprefix tailTrace_6221543
  have hstable : (prefixWord ++ tailWord_6221543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221543).length < 2 ^ (prefixWord ++ tailWord_6221543).sum := by decide
  have hdescent : baseEnd_6221543 < baseStart_6221543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221555 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_6221555 : Nat := 118140960795 + 6221555 * 2 ^ 59
def prefixEnd_6221555 : Nat := 4983230072969 + 3 ^ 40 * 6221555 * 2
def baseEnd_6221555 : Nat := 3194648133383510871150095

theorem tailTrace_6221555 : CollatzResearch.WordTrace tailWord_6221555 prefixEnd_6221555 3194648133383510871150095 := by
  unfold tailWord_6221555
  simp only [CollatzResearch.WordTrace]
  refine ⟨226918752975376266844626119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151279168650250844563084079 226918752975376266844626119)
  ·
    refine ⟨340378129463064400266939179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226918752975376266844626119 340378129463064400266939179)
    ·
      refine ⟨510567194194596600400408769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340378129463064400266939179 510567194194596600400408769)
      ·
        refine ⟨382925395645947450300306577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510567194194596600400408769 382925395645947450300306577)
        ·
          refine ⟨287194046734460587725229933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382925395645947450300306577 287194046734460587725229933)
          ·
            refine ⟨107697767525422720396961225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287194046734460587725229933 107697767525422720396961225)
            ·
              refine ⟨80773325644067040297720919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107697767525422720396961225 80773325644067040297720919)
              ·
                refine ⟨121159988466100560446581379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80773325644067040297720919 121159988466100560446581379)
                ·
                  refine ⟨181739982699150840669872069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121159988466100560446581379 181739982699150840669872069)
                  ·
                    refine ⟨34076246756090782625601013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181739982699150840669872069 34076246756090782625601013)
                    ·
                      refine ⟨3194648133383510871150095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34076246756090782625601013 3194648133383510871150095)
                      ·
                        rfl

theorem cell23_6221555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_6221555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221555 prefixEnd_6221555 := by exact prefixLift 6221555
  have htrace : WordTrace (prefixWord ++ tailWord_6221555) baseStart_6221555 baseEnd_6221555 := by
    simpa [prefixWord, tailWord_6221555, baseEnd_6221555] using wordTrace_append hprefix tailTrace_6221555
  have hstable : (prefixWord ++ tailWord_6221555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221555).length < 2 ^ (prefixWord ++ tailWord_6221555).sum := by decide
  have hdescent : baseEnd_6221555 < baseStart_6221555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221556 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6221556 : Nat := 118140960795 + 6221556 * 2 ^ 59
def prefixEnd_6221556 : Nat := 4983230072969 + 3 ^ 40 * 6221556 * 2
def baseEnd_6221556 : Nat := 3194648646864165367237591

theorem tailTrace_6221556 : CollatzResearch.WordTrace tailWord_6221556 prefixEnd_6221556 3194648646864165367237591 := by
  unfold tailWord_6221556
  simp only [CollatzResearch.WordTrace]
  refine ⟨113459394724186322007706261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151279192965581762676941681 113459394724186322007706261)
  ·
    refine ⟨5318409127696233844111231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113459394724186322007706261 5318409127696233844111231)
    ·
      refine ⟨7977613691544350766166847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318409127696233844111231 7977613691544350766166847)
      ·
        refine ⟨11966420537316526149250271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977613691544350766166847 11966420537316526149250271)
        ·
          refine ⟨17949630805974789223875407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966420537316526149250271 17949630805974789223875407)
          ·
            refine ⟨26924446208962183835813111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949630805974789223875407 26924446208962183835813111)
            ·
              refine ⟨40386669313443275753719667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26924446208962183835813111 40386669313443275753719667)
              ·
                refine ⟨60580003970164913630579501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40386669313443275753719667 60580003970164913630579501)
                ·
                  refine ⟨22717501488811842611467313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60580003970164913630579501 22717501488811842611467313)
                  ·
                    refine ⟨17038126116608881958600485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22717501488811842611467313 17038126116608881958600485)
                    ·
                      refine ⟨3194648646864165367237591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17038126116608881958600485 3194648646864165367237591)
                      ·
                        rfl

theorem cell23_6221556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6221556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221556 prefixEnd_6221556 := by exact prefixLift 6221556
  have htrace : WordTrace (prefixWord ++ tailWord_6221556) baseStart_6221556 baseEnd_6221556 := by
    simpa [prefixWord, tailWord_6221556, baseEnd_6221556] using wordTrace_append hprefix tailTrace_6221556
  have hstable : (prefixWord ++ tailWord_6221556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221556).length < 2 ^ (prefixWord ++ tailWord_6221556).sum := by decide
  have hdescent : baseEnd_6221556 < baseStart_6221556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221576 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_6221576 : Nat := 118140960795 + 6221576 * 2 ^ 59
def prefixEnd_6221576 : Nat := 4983230072969 + 3 ^ 40 * 6221576 * 2
def baseEnd_6221576 : Nat := 3194658916477255288987499

theorem tailTrace_6221576 : CollatzResearch.WordTrace tailWord_6221576 prefixEnd_6221576 3194658916477255288987499 := by
  unfold tailWord_6221576
  simp only [CollatzResearch.WordTrace]
  refine ⟨113459759454150093715570291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151279679272200124954093721 113459759454150093715570291)
  ·
    refine ⟨170189639181225140573355437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113459759454150093715570291 170189639181225140573355437)
    ·
      refine ⟨63821114692959427715008289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170189639181225140573355437 63821114692959427715008289)
      ·
        refine ⟨47865836019719570786256217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63821114692959427715008289 47865836019719570786256217)
        ·
          refine ⟨35899377014789678089692163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47865836019719570786256217 35899377014789678089692163)
          ·
            refine ⟨53849065522184517134538245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35899377014789678089692163 53849065522184517134538245)
            ·
              refine ⟨10096699785409596962725921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53849065522184517134538245 10096699785409596962725921)
              ·
                refine ⟨7572524839057197722044441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10096699785409596962725921 7572524839057197722044441)
                ·
                  refine ⟨5679393629292898291533331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7572524839057197722044441 5679393629292898291533331)
                  ·
                    refine ⟨8519090443939347437299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5679393629292898291533331 8519090443939347437299997)
                    ·
                      refine ⟨3194658916477255288987499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519090443939347437299997 3194658916477255288987499)
                      ·
                        rfl

theorem cell23_6221576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_6221576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221576 prefixEnd_6221576 := by exact prefixLift 6221576
  have htrace : WordTrace (prefixWord ++ tailWord_6221576) baseStart_6221576 baseEnd_6221576 := by
    simpa [prefixWord, tailWord_6221576, baseEnd_6221576] using wordTrace_append hprefix tailTrace_6221576
  have hstable : (prefixWord ++ tailWord_6221576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221576).length < 2 ^ (prefixWord ++ tailWord_6221576).sum := by decide
  have hdescent : baseEnd_6221576 < baseStart_6221576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221582 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6221582 : Nat := 118140960795 + 6221582 * 2 ^ 59
def prefixEnd_6221582 : Nat := 4983230072969 + 3 ^ 40 * 6221582 * 2
def baseEnd_6221582 : Nat := 3194661997361182265512471

theorem tailTrace_6221582 : CollatzResearch.WordTrace tailWord_6221582 prefixEnd_6221582 3194661997361182265512471 := by
  unfold tailWord_6221582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28364967218284806306982375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151279825164185633637239333 28364967218284806306982375)
  ·
    refine ⟨42547450827427209460473563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28364967218284806306982375 42547450827427209460473563)
    ·
      refine ⟨63821176241140814190710345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42547450827427209460473563 63821176241140814190710345)
      ·
        refine ⟨47865882180855610643032759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63821176241140814190710345 47865882180855610643032759)
        ·
          refine ⟨71798823271283415964549139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47865882180855610643032759 71798823271283415964549139)
          ·
            refine ⟨107698234906925123946823709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71798823271283415964549139 107698234906925123946823709)
            ·
              refine ⟨40386838090096921480058891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107698234906925123946823709 40386838090096921480058891)
              ·
                refine ⟨60580257135145382220088337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40386838090096921480058891 60580257135145382220088337)
                ·
                  refine ⟨45435192851359036665066253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60580257135145382220088337 45435192851359036665066253)
                  ·
                    refine ⟨17038197319259638749399845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45435192851359036665066253 17038197319259638749399845)
                    ·
                      refine ⟨3194661997361182265512471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17038197319259638749399845 3194661997361182265512471)
                      ·
                        rfl

theorem cell23_6221582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6221582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221582 prefixEnd_6221582 := by exact prefixLift 6221582
  have htrace : WordTrace (prefixWord ++ tailWord_6221582) baseStart_6221582 baseEnd_6221582 := by
    simpa [prefixWord, tailWord_6221582, baseEnd_6221582] using wordTrace_append hprefix tailTrace_6221582
  have hstable : (prefixWord ++ tailWord_6221582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221582).length < 2 ^ (prefixWord ++ tailWord_6221582).sum := by decide
  have hdescent : baseEnd_6221582 < baseStart_6221582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221595 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_6221595 : Nat := 118140960795 + 6221595 * 2 ^ 59
def prefixEnd_6221595 : Nat := 4983230072969 + 3 ^ 40 * 6221595 * 2
def baseEnd_6221595 : Nat := 3194668672609690714649911

theorem tailTrace_6221595 : CollatzResearch.WordTrace tailWord_6221595 prefixEnd_6221595 3194668672609690714649911 := by
  unfold tailWord_6221595
  simp only [CollatzResearch.WordTrace]
  refine ⟨226920211895231353676082239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151280141263487569117388159 226920211895231353676082239)
  ·
    refine ⟨340380317842847030514123359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226920211895231353676082239 340380317842847030514123359)
    ·
      refine ⟨510570476764270545771185039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340380317842847030514123359 510570476764270545771185039)
      ·
        refine ⟨765855715146405818656777559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510570476764270545771185039 765855715146405818656777559)
        ·
          refine ⟨1148783572719608727985166339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765855715146405818656777559 1148783572719608727985166339)
          ·
            refine ⟨1723175359079413091977749509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148783572719608727985166339 1723175359079413091977749509)
            ·
              refine ⟨323095379827389954745828033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1723175359079413091977749509 323095379827389954745828033)
              ·
                refine ⟨242321534870542466059371025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323095379827389954745828033 242321534870542466059371025)
                ·
                  refine ⟨181741151152906849544528269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242321534870542466059371025 181741151152906849544528269)
                  ·
                    refine ⟨68152931682340068579198101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181741151152906849544528269 68152931682340068579198101)
                    ·
                      refine ⟨3194668672609690714649911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68152931682340068579198101 3194668672609690714649911)
                      ·
                        rfl

theorem cell23_6221595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_6221595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221595 prefixEnd_6221595 := by exact prefixLift 6221595
  have htrace : WordTrace (prefixWord ++ tailWord_6221595) baseStart_6221595 baseEnd_6221595 := by
    simpa [prefixWord, tailWord_6221595, baseEnd_6221595] using wordTrace_append hprefix tailTrace_6221595
  have hstable : (prefixWord ++ tailWord_6221595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221595).length < 2 ^ (prefixWord ++ tailWord_6221595).sum := by decide
  have hdescent : baseEnd_6221595 < baseStart_6221595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221620 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6221620 : Nat := 118140960795 + 6221620 * 2 ^ 59
def prefixEnd_6221620 : Nat := 4983230072969 + 3 ^ 40 * 6221620 * 2
def baseEnd_6221620 : Nat := 3194681509626053116837297

theorem tailTrace_6221620 : CollatzResearch.WordTrace tailWord_6221620 prefixEnd_6221620 3194681509626053116837297 := by
  unfold tailWord_6221620
  simp only [CollatzResearch.WordTrace]
  refine ⟨113460561860070391472871157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151280749146760521963828209 113460561860070391472871157)
  ·
    refine ⟨10636927674381599200581671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113460561860070391472871157 10636927674381599200581671)
    ·
      refine ⟨15955391511572398800872507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10636927674381599200581671 15955391511572398800872507)
      ·
        refine ⟨23933087267358598201308761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15955391511572398800872507 23933087267358598201308761)
        ·
          refine ⟨17949815450518948650981571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23933087267358598201308761 17949815450518948650981571)
          ·
            refine ⟨26924723175778422976472357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949815450518948650981571 26924723175778422976472357)
            ·
              refine ⟨5048385595458454308088567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26924723175778422976472357 5048385595458454308088567)
              ·
                refine ⟨7572578393187681462132851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048385595458454308088567 7572578393187681462132851)
                ·
                  refine ⟨11358867589781522193199277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572578393187681462132851 11358867589781522193199277)
                  ·
                    refine ⟨4259575346168070822449729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11358867589781522193199277 4259575346168070822449729)
                    ·
                      refine ⟨3194681509626053116837297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259575346168070822449729 3194681509626053116837297)
                      ·
                        rfl

theorem cell23_6221620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6221620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221620 prefixEnd_6221620 := by exact prefixLift 6221620
  have htrace : WordTrace (prefixWord ++ tailWord_6221620) baseStart_6221620 baseEnd_6221620 := by
    simpa [prefixWord, tailWord_6221620, baseEnd_6221620] using wordTrace_append hprefix tailTrace_6221620
  have hstable : (prefixWord ++ tailWord_6221620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221620).length < 2 ^ (prefixWord ++ tailWord_6221620).sum := by decide
  have hdescent : baseEnd_6221620 < baseStart_6221620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221629 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6221629 : Nat := 118140960795 + 6221629 * 2 ^ 59
def prefixEnd_6221629 : Nat := 4983230072969 + 3 ^ 40 * 6221629 * 2
def baseEnd_6221629 : Nat := 3194686130951943581624755

theorem tailTrace_6221629 : CollatzResearch.WordTrace tailWord_6221629 prefixEnd_6221629 3194686130951943581624755 := by
  unfold tailWord_6221629
  simp only [CollatzResearch.WordTrace]
  refine ⟨226921451977108177482819941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151280967984738784988546627 226921451977108177482819941)
  ·
    refine ⟨42547772245707783278028739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226921451977108177482819941 42547772245707783278028739)
    ·
      refine ⟨63821658368561674917043109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42547772245707783278028739 63821658368561674917043109)
      ·
        refine ⟨11966560944105314046945583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63821658368561674917043109 11966560944105314046945583)
        ·
          refine ⟨17949841416157971070418375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11966560944105314046945583 17949841416157971070418375)
          ·
            refine ⟨26924762124236956605627563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949841416157971070418375 26924762124236956605627563)
            ·
              refine ⟨40387143186355434908441345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26924762124236956605627563 40387143186355434908441345)
              ·
                refine ⟨30290357389766576181331009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40387143186355434908441345 30290357389766576181331009)
                ·
                  refine ⟨22717768042324932135998257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30290357389766576181331009 22717768042324932135998257)
                  ·
                    refine ⟨17038326031743699101998693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22717768042324932135998257 17038326031743699101998693)
                    ·
                      refine ⟨3194686130951943581624755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17038326031743699101998693 3194686130951943581624755)
                      ·
                        rfl

theorem cell23_6221629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6221629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221629 prefixEnd_6221629 := by exact prefixLift 6221629
  have htrace : WordTrace (prefixWord ++ tailWord_6221629) baseStart_6221629 baseEnd_6221629 := by
    simpa [prefixWord, tailWord_6221629, baseEnd_6221629] using wordTrace_append hprefix tailTrace_6221629
  have hstable : (prefixWord ++ tailWord_6221629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221629).length < 2 ^ (prefixWord ++ tailWord_6221629).sum := by decide
  have hdescent : baseEnd_6221629 < baseStart_6221629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221639 : List Nat := [1, 1, 4, 1, 2, 1, 4, 4, 5]
def baseStart_6221639 : Nat := 118140960795 + 6221639 * 2 ^ 59
def prefixEnd_6221639 : Nat := 4983230072969 + 3 ^ 40 * 6221639 * 2
def baseEnd_6221639 : Nat := 354965696195387615833301

theorem tailTrace_6221639 : CollatzResearch.WordTrace tailWord_6221639 prefixEnd_6221639 354965696195387615833301 := by
  unfold tailWord_6221639
  simp only [CollatzResearch.WordTrace]
  refine ⟨226921816707071949190683971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151281211138047966127122647 226921816707071949190683971)
  ·
    refine ⟨340382725060607923786025957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226921816707071949190683971 340382725060607923786025957)
    ·
      refine ⟨63821760948863985709879867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 340382725060607923786025957 63821760948863985709879867)
      ·
        refine ⟨95732641423295978564819801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63821760948863985709879867 95732641423295978564819801)
        ·
          refine ⟨71799481067471983923614851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95732641423295978564819801 71799481067471983923614851)
          ·
            refine ⟨107699221601207975885422277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71799481067471983923614851 107699221601207975885422277)
            ·
              refine ⟨20193604050226495478516677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107699221601207975885422277 20193604050226495478516677)
              ·
                refine ⟨3786300759417467902221877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20193604050226495478516677 3786300759417467902221877)
                ·
                  refine ⟨354965696195387615833301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786300759417467902221877 354965696195387615833301)
                  ·
                    rfl

theorem cell23_6221639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 4, 5].length) (baseStart_6221639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221639 prefixEnd_6221639 := by exact prefixLift 6221639
  have htrace : WordTrace (prefixWord ++ tailWord_6221639) baseStart_6221639 baseEnd_6221639 := by
    simpa [prefixWord, tailWord_6221639, baseEnd_6221639] using wordTrace_append hprefix tailTrace_6221639
  have hstable : (prefixWord ++ tailWord_6221639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221639).length < 2 ^ (prefixWord ++ tailWord_6221639).sum := by decide
  have hdescent : baseEnd_6221639 < baseStart_6221639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221649 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_6221649 : Nat := 118140960795 + 6221649 * 2 ^ 59
def prefixEnd_6221649 : Nat := 4983230072969 + 3 ^ 40 * 6221649 * 2
def baseEnd_6221649 : Nat := 3194696400565033503374663

theorem tailTrace_6221649 : CollatzResearch.WordTrace tailWord_6221649 prefixEnd_6221649 3194696400565033503374663 := by
  unfold tailWord_6221649
  simp only [CollatzResearch.WordTrace]
  refine ⟨226922181437035720898548001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151281454291357147265698667 226922181437035720898548001)
  ·
    refine ⟨170191636077776790673911001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226922181437035720898548001 170191636077776790673911001)
    ·
      refine ⟨127643727058332593005433251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170191636077776790673911001 127643727058332593005433251)
      ·
        refine ⟨191465590587498889508149877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127643727058332593005433251 191465590587498889508149877)
        ·
          refine ⟨17949899117578020891389051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191465590587498889508149877 17949899117578020891389051)
          ·
            refine ⟨26924848676367031337083577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17949899117578020891389051 26924848676367031337083577)
            ·
              refine ⟨20193636507275273502812683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26924848676367031337083577 20193636507275273502812683)
              ·
                refine ⟨30290454760912910254219025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20193636507275273502812683 30290454760912910254219025)
                ·
                  refine ⟨22717841070684682690664269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30290454760912910254219025 22717841070684682690664269)
                  ·
                    refine ⟨8519190401506756008999101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22717841070684682690664269 8519190401506756008999101)
                    ·
                      refine ⟨3194696400565033503374663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519190401506756008999101 3194696400565033503374663)
                      ·
                        rfl

theorem cell23_6221649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_6221649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221649 prefixEnd_6221649 := by exact prefixLift 6221649
  have htrace : WordTrace (prefixWord ++ tailWord_6221649) baseStart_6221649 baseEnd_6221649 := by
    simpa [prefixWord, tailWord_6221649, baseEnd_6221649] using wordTrace_append hprefix tailTrace_6221649
  have hstable : (prefixWord ++ tailWord_6221649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221649).length < 2 ^ (prefixWord ++ tailWord_6221649).sum := by decide
  have hdescent : baseEnd_6221649 < baseStart_6221649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221650 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_6221650 : Nat := 118140960795 + 6221650 * 2 ^ 59
def prefixEnd_6221650 : Nat := 4983230072969 + 3 ^ 40 * 6221650 * 2
def baseEnd_6221650 : Nat := 3194696914045687999462159

theorem tailTrace_6221650 : CollatzResearch.WordTrace tailWord_6221650 prefixEnd_6221650 3194696914045687999462159 := by
  unfold tailWord_6221650
  simp only [CollatzResearch.WordTrace]
  refine ⟨56730554477508024517333601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151281478606688065379556269 56730554477508024517333601)
  ·
    refine ⟨42547915858131018388000201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56730554477508024517333601 42547915858131018388000201)
    ·
      refine ⟨31910936893598263791000151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42547915858131018388000201 31910936893598263791000151)
      ·
        refine ⟨47866405340397395686500227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31910936893598263791000151 47866405340397395686500227)
        ·
          refine ⟨71799608010596093529750341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47866405340397395686500227 71799608010596093529750341)
          ·
            refine ⟨13462426501986767536828189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71799608010596093529750341 13462426501986767536828189)
            ·
              refine ⟨5048409938245037826310571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13462426501986767536828189 5048409938245037826310571)
              ·
                refine ⟨7572614907367556739465857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048409938245037826310571 7572614907367556739465857)
                ·
                  refine ⟨5679461180525667554599393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7572614907367556739465857 5679461180525667554599393)
                  ·
                    refine ⟨4259595885394250665949545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679461180525667554599393 4259595885394250665949545)
                    ·
                      refine ⟨3194696914045687999462159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259595885394250665949545 3194696914045687999462159)
                      ·
                        rfl

theorem cell23_6221650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_6221650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221650 prefixEnd_6221650 := by exact prefixLift 6221650
  have htrace : WordTrace (prefixWord ++ tailWord_6221650) baseStart_6221650 baseEnd_6221650 := by
    simpa [prefixWord, tailWord_6221650, baseEnd_6221650] using wordTrace_append hprefix tailTrace_6221650
  have hstable : (prefixWord ++ tailWord_6221650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221650).length < 2 ^ (prefixWord ++ tailWord_6221650).sum := by decide
  have hdescent : baseEnd_6221650 < baseStart_6221650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221689 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6221689 : Nat := 118140960795 + 6221689 * 2 ^ 59
def prefixEnd_6221689 : Nat := 4983230072969 + 3 ^ 40 * 6221689 * 2
def baseEnd_6221689 : Nat := 3194716939791213346874479

theorem tailTrace_6221689 : CollatzResearch.WordTrace tailWord_6221689 prefixEnd_6221689 3194716939791213346874479 := by
  unfold tailWord_6221689
  simp only [CollatzResearch.WordTrace]
  refine ⟨226923640356890807730004121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151282426904593871820002747 226923640356890807730004121)
  ·
    refine ⟨170192730267668105797503091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226923640356890807730004121 170192730267668105797503091)
    ·
      refine ⟨255289095401502158696254637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170192730267668105797503091 255289095401502158696254637)
      ·
        refine ⟨95733410775563309511095489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255289095401502158696254637 95733410775563309511095489)
        ·
          refine ⟨71800058081672482133321617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95733410775563309511095489 71800058081672482133321617)
          ·
            refine ⟨53850043561254361599991213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71800058081672482133321617 53850043561254361599991213)
            ·
              refine ⟨20193766335470385599996705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53850043561254361599991213 20193766335470385599996705)
              ·
                refine ⟨15145324751602789199997529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20193766335470385599996705 15145324751602789199997529)
                ·
                  refine ⟨11358993563702091899998147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15145324751602789199997529 11358993563702091899998147)
                  ·
                    refine ⟨17038490345553137849997221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11358993563702091899998147 17038490345553137849997221)
                    ·
                      refine ⟨3194716939791213346874479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17038490345553137849997221 3194716939791213346874479)
                      ·
                        rfl

theorem cell23_6221689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6221689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221689 prefixEnd_6221689 := by exact prefixLift 6221689
  have htrace : WordTrace (prefixWord ++ tailWord_6221689) baseStart_6221689 baseEnd_6221689 := by
    simpa [prefixWord, tailWord_6221689, baseEnd_6221689] using wordTrace_append hprefix tailTrace_6221689
  have hstable : (prefixWord ++ tailWord_6221689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221689).length < 2 ^ (prefixWord ++ tailWord_6221689).sum := by decide
  have hdescent : baseEnd_6221689 < baseStart_6221689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221796 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_6221796 : Nat := 118140960795 + 6221796 * 2 ^ 59
def prefixEnd_6221796 : Nat := 4983230072969 + 3 ^ 40 * 6221796 * 2
def baseEnd_6221796 : Nat := 3194771882221244428236487

theorem tailTrace_6221796 : CollatzResearch.WordTrace tailWord_6221796 prefixEnd_6221796 3194771882221244428236487 := by
  unfold tailWord_6221796
  simp only [CollatzResearch.WordTrace]
  refine ⟨113463771483751582502074621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151285028645002110002766161 113463771483751582502074621)
  ·
    refine ⟨42548914306406843438277983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113463771483751582502074621 42548914306406843438277983)
    ·
      refine ⟨63823371459610265157416975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42548914306406843438277983 63823371459610265157416975)
      ·
        refine ⟨95735057189415397736125463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63823371459610265157416975 95735057189415397736125463)
        ·
          refine ⟨143602585784123096604188195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95735057189415397736125463 143602585784123096604188195)
          ·
            refine ⟨215403878676184644906282293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143602585784123096604188195 215403878676184644906282293)
            ·
              refine ⟨20194113625892310459963965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215403878676184644906282293 20194113625892310459963965)
              ·
                refine ⟨7572792609709616422486487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20194113625892310459963965 7572792609709616422486487)
                ·
                  refine ⟨11359188914564424633729731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7572792609709616422486487 11359188914564424633729731)
                  ·
                    refine ⟨17038783371846636950594597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11359188914564424633729731 17038783371846636950594597)
                    ·
                      refine ⟨3194771882221244428236487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17038783371846636950594597 3194771882221244428236487)
                      ·
                        rfl

theorem cell23_6221796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_6221796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221796 prefixEnd_6221796 := by exact prefixLift 6221796
  have htrace : WordTrace (prefixWord ++ tailWord_6221796) baseStart_6221796 baseEnd_6221796 := by
    simpa [prefixWord, tailWord_6221796, baseEnd_6221796] using wordTrace_append hprefix tailTrace_6221796
  have hstable : (prefixWord ++ tailWord_6221796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221796).length < 2 ^ (prefixWord ++ tailWord_6221796).sum := by decide
  have hdescent : baseEnd_6221796 < baseStart_6221796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221859 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_6221859 : Nat := 118140960795 + 6221859 * 2 ^ 59
def prefixEnd_6221859 : Nat := 4983230072969 + 3 ^ 40 * 6221859 * 2
def baseEnd_6221859 : Nat := 3194804231502477681748697

theorem tailTrace_6221859 : CollatzResearch.WordTrace tailWord_6221859 prefixEnd_6221859 3194804231502477681748697 := by
  unfold tailWord_6221859
  simp only [CollatzResearch.WordTrace]
  refine ⟨226929840766274926763692631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151286560510849951175795087 226929840766274926763692631)
  ·
    refine ⟨340394761149412390145538947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226929840766274926763692631 340394761149412390145538947)
    ·
      refine ⟨510592141724118585218308421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340394761149412390145538947 510592141724118585218308421)
      ·
        refine ⟨95736026573272234728432829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 510592141724118585218308421 95736026573272234728432829)
        ·
          refine ⟨35901009964977088023162311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95736026573272234728432829 35901009964977088023162311)
          ·
            refine ⟨53851514947465632034743467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35901009964977088023162311 53851514947465632034743467)
            ·
              refine ⟨80777272421198448052115201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53851514947465632034743467 80777272421198448052115201)
              ·
                refine ⟨60582954315898836039086401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80777272421198448052115201 60582954315898836039086401)
                ·
                  refine ⟨45437215736924127029314801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60582954315898836039086401 45437215736924127029314801)
                  ·
                    refine ⟨34077911802693095271986101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45437215736924127029314801 34077911802693095271986101)
                    ·
                      refine ⟨3194804231502477681748697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34077911802693095271986101 3194804231502477681748697)
                      ·
                        rfl

theorem cell23_6221859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_6221859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221859 prefixEnd_6221859 := by exact prefixLift 6221859
  have htrace : WordTrace (prefixWord ++ tailWord_6221859) baseStart_6221859 baseEnd_6221859 := by
    simpa [prefixWord, tailWord_6221859, baseEnd_6221859] using wordTrace_append hprefix tailTrace_6221859
  have hstable : (prefixWord ++ tailWord_6221859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221859).length < 2 ^ (prefixWord ++ tailWord_6221859).sum := by decide
  have hdescent : baseEnd_6221859 < baseStart_6221859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221864 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6221864 : Nat := 118140960795 + 6221864 * 2 ^ 59
def prefixEnd_6221864 : Nat := 4983230072969 + 3 ^ 40 * 6221864 * 2
def baseEnd_6221864 : Nat := 3194806798905750162186175

theorem tailTrace_6221864 : CollatzResearch.WordTrace tailWord_6221864 prefixEnd_6221864 3194806798905750162186175 := by
  unfold tailWord_6221864
  simp only [CollatzResearch.WordTrace]
  refine ⟨113465011565628406308812323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151286682087504541745083097 113465011565628406308812323)
  ·
    refine ⟨170197517348442609463218485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113465011565628406308812323 170197517348442609463218485)
    ·
      refine ⟨15956017251416494637176733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170197517348442609463218485 15956017251416494637176733)
      ·
        refine ⟨5983506469281185488941275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15956017251416494637176733 5983506469281185488941275)
        ·
          refine ⟨8975259703921778233411913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983506469281185488941275 8975259703921778233411913)
          ·
            refine ⟨6731444777941333675058935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8975259703921778233411913 6731444777941333675058935)
            ·
              refine ⟨10097167166912000512588403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731444777941333675058935 10097167166912000512588403)
              ·
                refine ⟨15145750750368000768882605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10097167166912000512588403 15145750750368000768882605)
                ·
                  refine ⟨5679656531388000288330977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15145750750368000768882605 5679656531388000288330977)
                  ·
                    refine ⟨4259742398541000216248233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679656531388000288330977 4259742398541000216248233)
                    ·
                      refine ⟨3194806798905750162186175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259742398541000216248233 3194806798905750162186175)
                      ·
                        rfl

theorem cell23_6221864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6221864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221864 prefixEnd_6221864 := by exact prefixLift 6221864
  have htrace : WordTrace (prefixWord ++ tailWord_6221864) baseStart_6221864 baseEnd_6221864 := by
    simpa [prefixWord, tailWord_6221864, baseEnd_6221864] using wordTrace_append hprefix tailTrace_6221864
  have hstable : (prefixWord ++ tailWord_6221864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221864).length < 2 ^ (prefixWord ++ tailWord_6221864).sum := by decide
  have hdescent : baseEnd_6221864 < baseStart_6221864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221879 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 2, 6]
def baseStart_6221879 : Nat := 118140960795 + 6221879 * 2 ^ 59
def prefixEnd_6221879 : Nat := 4983230072969 + 3 ^ 40 * 6221879 * 2
def baseEnd_6221879 : Nat := 1064938167038522534499535

theorem tailTrace_6221879 : CollatzResearch.WordTrace tailWord_6221879 prefixEnd_6221879 1064938167038522534499535 := by
  unfold tailWord_6221879
  simp only [CollatzResearch.WordTrace]
  refine ⟨226930570226202470179420691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151287046817468313452947127 226930570226202470179420691)
  ·
    refine ⟨340395855339303705269131037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226930570226202470179420691 340395855339303705269131037)
    ·
      refine ⟨127648445752238889475924139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340395855339303705269131037 127648445752238889475924139)
      ·
        refine ⟨191472668628358334213886209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127648445752238889475924139 191472668628358334213886209)
        ·
          refine ⟨143604501471268750660414657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191472668628358334213886209 143604501471268750660414657)
          ·
            refine ⟨107703376103451562995310993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143604501471268750660414657 107703376103451562995310993)
            ·
              refine ⟨80777532077588672246483245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107703376103451562995310993 80777532077588672246483245)
              ·
                refine ⟨30291574529095752092431217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80777532077588672246483245 30291574529095752092431217)
                ·
                  refine ⟨22718680896821814069323413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30291574529095752092431217 22718680896821814069323413)
                  ·
                    refine ⟨1064938167038522534499535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22718680896821814069323413 1064938167038522534499535)
                    ·
                      rfl

theorem cell23_6221879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_6221879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221879 prefixEnd_6221879 := by exact prefixLift 6221879
  have htrace : WordTrace (prefixWord ++ tailWord_6221879) baseStart_6221879 baseEnd_6221879 := by
    simpa [prefixWord, tailWord_6221879, baseEnd_6221879] using wordTrace_append hprefix tailTrace_6221879
  have hstable : (prefixWord ++ tailWord_6221879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221879).length < 2 ^ (prefixWord ++ tailWord_6221879).sum := by decide
  have hdescent : baseEnd_6221879 < baseStart_6221879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221880 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_6221880 : Nat := 118140960795 + 6221880 * 2 ^ 59
def prefixEnd_6221880 : Nat := 4983230072969 + 3 ^ 40 * 6221880 * 2
def baseEnd_6221880 : Nat := 3194815014596222099586101

theorem tailTrace_6221880 : CollatzResearch.WordTrace tailWord_6221880 prefixEnd_6221880 3194815014596222099586101 := by
  unfold tailWord_6221880
  simp only [CollatzResearch.WordTrace]
  refine ⟨113465303349599423675103547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151287071132799231566804729 113465303349599423675103547)
  ·
    refine ⟨170197955024399135512655321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113465303349599423675103547 170197955024399135512655321)
    ·
      refine ⟨127648466268299351634491491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170197955024399135512655321 127648466268299351634491491)
      ·
        refine ⟨191472699402449027451737237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127648466268299351634491491 191472699402449027451737237)
        ·
          refine ⟨8975282784489798161800183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 191472699402449027451737237 8975282784489798161800183)
          ·
            refine ⟨13462924176734697242700275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8975282784489798161800183 13462924176734697242700275)
            ·
              refine ⟨20194386265102045864050413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13462924176734697242700275 20194386265102045864050413)
              ·
                refine ⟨7572894849413267199018905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20194386265102045864050413 7572894849413267199018905)
                ·
                  refine ⟨5679671137059950399264179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7572894849413267199018905 5679671137059950399264179)
                  ·
                    refine ⟨8519506705589925598896269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5679671137059950399264179 8519506705589925598896269)
                    ·
                      refine ⟨3194815014596222099586101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519506705589925598896269 3194815014596222099586101)
                      ·
                        rfl

theorem cell23_6221880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_6221880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221880 prefixEnd_6221880 := by exact prefixLift 6221880
  have htrace : WordTrace (prefixWord ++ tailWord_6221880) baseStart_6221880 baseEnd_6221880 := by
    simpa [prefixWord, tailWord_6221880, baseEnd_6221880] using wordTrace_append hprefix tailTrace_6221880
  have hstable : (prefixWord ++ tailWord_6221880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221880).length < 2 ^ (prefixWord ++ tailWord_6221880).sum := by decide
  have hdescent : baseEnd_6221880 < baseStart_6221880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221899 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_6221899 : Nat := 118140960795 + 6221899 * 2 ^ 59
def prefixEnd_6221899 : Nat := 4983230072969 + 3 ^ 40 * 6221899 * 2
def baseEnd_6221899 : Nat := 3194824770728657525248513

theorem tailTrace_6221899 : CollatzResearch.WordTrace tailWord_6221899 prefixEnd_6221899 3194824770728657525248513 := by
  unfold tailWord_6221899
  simp only [CollatzResearch.WordTrace]
  refine ⟨226931299686130013595148751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151287533124086675730099167 226931299686130013595148751)
  ·
    refine ⟨340396949529195020392723127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226931299686130013595148751 340396949529195020392723127)
    ·
      refine ⟨510595424293792530589084691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340396949529195020392723127 510595424293792530589084691)
      ·
        refine ⟨765893136440688795883627037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510595424293792530589084691 765893136440688795883627037)
        ·
          refine ⟨287209926165258298456360139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 765893136440688795883627037 287209926165258298456360139)
          ·
            refine ⟨430814889247887447684540209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287209926165258298456360139 430814889247887447684540209)
            ·
              refine ⟨323111166935915585763405157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430814889247887447684540209 323111166935915585763405157)
              ·
                refine ⟨60583343800484172330638467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323111166935915585763405157 60583343800484172330638467)
                ·
                  refine ⟨90875015700726258495957701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60583343800484172330638467 90875015700726258495957701)
                  ·
                    refine ⟨17039065443886173467992069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90875015700726258495957701 17039065443886173467992069)
                    ·
                      refine ⟨3194824770728657525248513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17039065443886173467992069 3194824770728657525248513)
                      ·
                        rfl

theorem cell23_6221899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_6221899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221899 prefixEnd_6221899 := by exact prefixLift 6221899
  have htrace : WordTrace (prefixWord ++ tailWord_6221899) baseStart_6221899 baseEnd_6221899 := by
    simpa [prefixWord, tailWord_6221899, baseEnd_6221899] using wordTrace_append hprefix tailTrace_6221899
  have hstable : (prefixWord ++ tailWord_6221899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221899).length < 2 ^ (prefixWord ++ tailWord_6221899).sum := by decide
  have hdescent : baseEnd_6221899 < baseStart_6221899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221920 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2]
def baseStart_6221920 : Nat := 118140960795 + 6221920 * 2 ^ 59
def prefixEnd_6221920 : Nat := 4983230072969 + 3 ^ 40 * 6221920 * 2
def baseEnd_6221920 : Nat := 3194835553822401943085917

theorem tailTrace_6221920 : CollatzResearch.WordTrace tailWord_6221920 prefixEnd_6221920 3194835553822401943085917 := by
  unfold tailWord_6221920
  simp only [CollatzResearch.WordTrace]
  refine ⟨113466032809526967090831607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151288043746035956121108809 113466032809526967090831607)
  ·
    refine ⟨170199049214290450636247411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113466032809526967090831607 170199049214290450636247411)
    ·
      refine ⟨255298573821435675954371117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170199049214290450636247411 255298573821435675954371117)
      ·
        refine ⟨95736965183038378482889169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255298573821435675954371117 95736965183038378482889169)
        ·
          refine ⟨71802723887278783862166877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95736965183038378482889169 71802723887278783862166877)
          ·
            refine ⟨26926021457729543948312579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71802723887278783862166877 26926021457729543948312579)
            ·
              refine ⟨40389032186594315922468869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26926021457729543948312579 40389032186594315922468869)
              ·
                refine ⟨7572943534986434235462913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40389032186594315922468869 7572943534986434235462913)
                ·
                  refine ⟨5679707651239825676597185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7572943534986434235462913 5679707651239825676597185)
                  ·
                    refine ⟨4259780738429869257447889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5679707651239825676597185 4259780738429869257447889)
                    ·
                      refine ⟨3194835553822401943085917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259780738429869257447889 3194835553822401943085917)
                      ·
                        rfl

theorem cell23_6221920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_6221920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221920 prefixEnd_6221920 := by exact prefixLift 6221920
  have htrace : WordTrace (prefixWord ++ tailWord_6221920) baseStart_6221920 baseEnd_6221920 := by
    simpa [prefixWord, tailWord_6221920, baseEnd_6221920] using wordTrace_append hprefix tailTrace_6221920
  have hstable : (prefixWord ++ tailWord_6221920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221920).length < 2 ^ (prefixWord ++ tailWord_6221920).sum := by decide
  have hdescent : baseEnd_6221920 < baseStart_6221920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221936 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_6221936 : Nat := 118140960795 + 6221936 * 2 ^ 59
def prefixEnd_6221936 : Nat := 4983230072969 + 3 ^ 40 * 6221936 * 2
def baseEnd_6221936 : Nat := 3194843769512873880485843

theorem tailTrace_6221936 : CollatzResearch.WordTrace tailWord_6221936 prefixEnd_6221936 3194843769512873880485843 := by
  unfold tailWord_6221936
  simp only [CollatzResearch.WordTrace]
  refine ⟨113466324593497984457122831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151288432791330645942830441 113466324593497984457122831)
  ·
    refine ⟨170199486890246976685684247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113466324593497984457122831 170199486890246976685684247)
    ·
      refine ⟨255299230335370465028526371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170199486890246976685684247 255299230335370465028526371)
      ·
        refine ⟨382948845503055697542789557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255299230335370465028526371 382948845503055697542789557)
        ·
          refine ⟨35901454265911471644636521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382948845503055697542789557 35901454265911471644636521)
          ·
            refine ⟨26926090699433603733477391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35901454265911471644636521 26926090699433603733477391)
            ·
              refine ⟨40389136049150405600216087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26926090699433603733477391 40389136049150405600216087)
              ·
                refine ⟨60583704073725608400324131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40389136049150405600216087 60583704073725608400324131)
                ·
                  refine ⟨90875556110588412600486197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60583704073725608400324131 90875556110588412600486197)
                  ·
                    refine ⟨8519583385367663681295581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90875556110588412600486197 8519583385367663681295581)
                    ·
                      refine ⟨3194843769512873880485843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519583385367663681295581 3194843769512873880485843)
                      ·
                        rfl

theorem cell23_6221936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_6221936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221936 prefixEnd_6221936 := by exact prefixLift 6221936
  have htrace : WordTrace (prefixWord ++ tailWord_6221936) baseStart_6221936 baseEnd_6221936 := by
    simpa [prefixWord, tailWord_6221936, baseEnd_6221936] using wordTrace_append hprefix tailTrace_6221936
  have hstable : (prefixWord ++ tailWord_6221936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221936).length < 2 ^ (prefixWord ++ tailWord_6221936).sum := by decide
  have hdescent : baseEnd_6221936 < baseStart_6221936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221956 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_6221956 : Nat := 118140960795 + 6221956 * 2 ^ 59
def prefixEnd_6221956 : Nat := 4983230072969 + 3 ^ 40 * 6221956 * 2
def baseEnd_6221956 : Nat := 1064951346375321267411917

theorem tailTrace_6221956 : CollatzResearch.WordTrace tailWord_6221956 prefixEnd_6221956 1064951346375321267411917 := by
  unfold tailWord_6221956
  simp only [CollatzResearch.WordTrace]
  refine ⟨113466689323461756164986861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151288919097949008219982481 113466689323461756164986861)
  ·
    refine ⟨42550008496298158561870073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113466689323461756164986861 42550008496298158561870073)
    ·
      refine ⟨31912506372223618921402555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42550008496298158561870073 31912506372223618921402555)
      ·
        refine ⟨47868759558335428382103833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31912506372223618921402555 47868759558335428382103833)
        ·
          refine ⟨35901569668751571286577875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47868759558335428382103833 35901569668751571286577875)
          ·
            refine ⟨53852354503127356929866813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35901569668751571286577875 53852354503127356929866813)
            ·
              refine ⟨20194632938672758848700055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53852354503127356929866813 20194632938672758848700055)
              ·
                refine ⟨30291949408009138273050083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20194632938672758848700055 30291949408009138273050083)
                ·
                  refine ⟨45437924112013707409575125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30291949408009138273050083 45437924112013707409575125)
                  ·
                    refine ⟨1064951346375321267411917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45437924112013707409575125 1064951346375321267411917)
                    ·
                      rfl

theorem cell23_6221956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_6221956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221956 prefixEnd_6221956 := by exact prefixLift 6221956
  have htrace : WordTrace (prefixWord ++ tailWord_6221956) baseStart_6221956 baseEnd_6221956 := by
    simpa [prefixWord, tailWord_6221956, baseEnd_6221956] using wordTrace_append hprefix tailTrace_6221956
  have hstable : (prefixWord ++ tailWord_6221956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221956).length < 2 ^ (prefixWord ++ tailWord_6221956).sum := by decide
  have hdescent : baseEnd_6221956 < baseStart_6221956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221960 : List Nat := [2, 1, 3, 4, 1, 2, 2, 3, 5]
def baseStart_6221960 : Nat := 118140960795 + 6221960 * 2 ^ 59
def prefixEnd_6221960 : Nat := 4983230072969 + 3 ^ 40 * 6221960 * 2
def baseEnd_6221960 : Nat := 354984010338731309620637

theorem tailTrace_6221960 : CollatzResearch.WordTrace tailWord_6221960 prefixEnd_6221960 354984010338731309620637 := by
  unfold tailWord_6221960
  simp only [CollatzResearch.WordTrace]
  refine ⟨113466762269454510506559667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151289016359272680675412889 113466762269454510506559667)
  ·
    refine ⟨170200143404181765759839501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113466762269454510506559667 170200143404181765759839501)
    ·
      refine ⟨63825053776568162159939813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170200143404181765759839501 63825053776568162159939813)
      ·
        refine ⟨11967197583106530404988715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63825053776568162159939813 11967197583106530404988715)
        ·
          refine ⟨17950796374659795607483073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967197583106530404988715 17950796374659795607483073)
          ·
            refine ⟨13463097280994846705612305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17950796374659795607483073 13463097280994846705612305)
            ·
              refine ⟨10097322960746135029209229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13463097280994846705612305 10097322960746135029209229)
              ·
                refine ⟨3786496110279800635953461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10097322960746135029209229 3786496110279800635953461)
                ·
                  refine ⟨354984010338731309620637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786496110279800635953461 354984010338731309620637)
                  ·
                    rfl

theorem cell23_6221960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3, 5].length) (baseStart_6221960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221960 prefixEnd_6221960 := by exact prefixLift 6221960
  have htrace : WordTrace (prefixWord ++ tailWord_6221960) baseStart_6221960 baseEnd_6221960 := by
    simpa [prefixWord, tailWord_6221960, baseEnd_6221960] using wordTrace_append hprefix tailTrace_6221960
  have hstable : (prefixWord ++ tailWord_6221960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221960).length < 2 ^ (prefixWord ++ tailWord_6221960).sum := by decide
  have hdescent : baseEnd_6221960 < baseStart_6221960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6221969 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_6221969 : Nat := 118140960795 + 6221969 * 2 ^ 59
def prefixEnd_6221969 : Nat := 4983230072969 + 3 ^ 40 * 6221969 * 2
def baseEnd_6221969 : Nat := 1064953571458157417124397

theorem tailTrace_6221969 : CollatzResearch.WordTrace tailWord_6221969 prefixEnd_6221969 1064953571458157417124397 := by
  unfold tailWord_6221969
  simp only [CollatzResearch.WordTrace]
  refine ⟨226933852795876415550196961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151289235197250943700131307 226933852795876415550196961)
  ·
    refine ⟨170200389596907311662647721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226933852795876415550196961 170200389596907311662647721)
    ·
      refine ⟨127650292197680483746985791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170200389596907311662647721 127650292197680483746985791)
      ·
        refine ⟨191475438296520725620478687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127650292197680483746985791 191475438296520725620478687)
        ·
          refine ⟨287213157444781088430718031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191475438296520725620478687 287213157444781088430718031)
          ·
            refine ⟨430819736167171632646077047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287213157444781088430718031 430819736167171632646077047)
            ·
              refine ⟨646229604250757448969115571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430819736167171632646077047 646229604250757448969115571)
              ·
                refine ⟨969344406376136173453673357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646229604250757448969115571 969344406376136173453673357)
                ·
                  refine ⟨363504152391051065045127509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969344406376136173453673357 363504152391051065045127509)
                  ·
                    refine ⟨1064953571458157417124397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 363504152391051065045127509 1064953571458157417124397)
                    ·
                      rfl

theorem cell23_6221969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_6221969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6221969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6221969 prefixEnd_6221969 := by exact prefixLift 6221969
  have htrace : WordTrace (prefixWord ++ tailWord_6221969) baseStart_6221969 baseEnd_6221969 := by
    simpa [prefixWord, tailWord_6221969, baseEnd_6221969] using wordTrace_append hprefix tailTrace_6221969
  have hstable : (prefixWord ++ tailWord_6221969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6221969).length < 2 ^ (prefixWord ++ tailWord_6221969).sum := by decide
  have hdescent : baseEnd_6221969 < baseStart_6221969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6221969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222013 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_6222013 : Nat := 118140960795 + 6222013 * 2 ^ 59
def prefixEnd_6222013 : Nat := 4983230072969 + 3 ^ 40 * 6222013 * 2
def baseEnd_6222013 : Nat := 3194883307523270079222989

theorem tailTrace_6222013 : CollatzResearch.WordTrace tailWord_6222013 prefixEnd_6222013 3194883307523270079222989 := by
  unfold tailWord_6222013
  simp only [CollatzResearch.WordTrace]
  refine ⟨226935457607717011064798693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151290305071811340709865795 226935457607717011064798693)
  ·
    refine ⟨42550398301446939574649755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226935457607717011064798693 42550398301446939574649755)
    ·
      refine ⟨63825597452170409361974633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42550398301446939574649755 63825597452170409361974633)
      ·
        refine ⟨47869198089127807021480975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63825597452170409361974633 47869198089127807021480975)
        ·
          refine ⟨71803797133691710532221463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47869198089127807021480975 71803797133691710532221463)
          ·
            refine ⟨107705695700537565798332195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71803797133691710532221463 107705695700537565798332195)
            ·
              refine ⟨161558543550806348697498293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107705695700537565798332195 161558543550806348697498293)
              ·
                refine ⟨15146113457888095190390465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161558543550806348697498293 15146113457888095190390465)
                ·
                  refine ⟨11359585093416071392792849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15146113457888095190390465 11359585093416071392792849)
                  ·
                    refine ⟨8519688820062053544594637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11359585093416071392792849 8519688820062053544594637)
                    ·
                      refine ⟨3194883307523270079222989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519688820062053544594637 3194883307523270079222989)
                      ·
                        rfl

theorem cell23_6222013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_6222013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222013 prefixEnd_6222013 := by exact prefixLift 6222013
  have htrace : WordTrace (prefixWord ++ tailWord_6222013) baseStart_6222013 baseEnd_6222013 := by
    simpa [prefixWord, tailWord_6222013, baseEnd_6222013] using wordTrace_append hprefix tailTrace_6222013
  have hstable : (prefixWord ++ tailWord_6222013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222013).length < 2 ^ (prefixWord ++ tailWord_6222013).sum := by decide
  have hdescent : baseEnd_6222013 < baseStart_6222013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222016 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 8]
def baseStart_6222016 : Nat := 118140960795 + 6222016 * 2 ^ 59
def prefixEnd_6222016 : Nat := 4983230072969 + 3 ^ 40 * 6222016 * 2
def baseEnd_6222016 : Nat := 354987205329470396387275

theorem tailTrace_6222016 : CollatzResearch.WordTrace tailWord_6222016 prefixEnd_6222016 354987205329470396387275 := by
  unfold tailWord_6222016
  simp only [CollatzResearch.WordTrace]
  refine ⟨113467783513353071288578951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151290378017804095051438601 113467783513353071288578951)
  ·
    refine ⟨170201675270029606932868427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113467783513353071288578951 170201675270029606932868427)
    ·
      refine ⟨255302512905044410399302641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170201675270029606932868427 255302512905044410399302641)
      ·
        refine ⟨191476884678783307799476981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255302512905044410399302641 191476884678783307799476981)
        ·
          refine ⟨17950957938635935106200967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191476884678783307799476981 17950957938635935106200967)
          ·
            refine ⟨26926436907953902659301451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17950957938635935106200967 26926436907953902659301451)
            ·
              refine ⟨40389655361930853988952177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26926436907953902659301451 40389655361930853988952177)
              ·
                refine ⟨30292241521448140491714133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40389655361930853988952177 30292241521448140491714133)
                ·
                  refine ⟨354987205329470396387275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30292241521448140491714133 354987205329470396387275)
                  ·
                    rfl

theorem cell23_6222016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_6222016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222016 prefixEnd_6222016 := by exact prefixLift 6222016
  have htrace : WordTrace (prefixWord ++ tailWord_6222016) baseStart_6222016 baseEnd_6222016 := by
    simpa [prefixWord, tailWord_6222016, baseEnd_6222016] using wordTrace_append hprefix tailTrace_6222016
  have hstable : (prefixWord ++ tailWord_6222016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222016).length < 2 ^ (prefixWord ++ tailWord_6222016).sum := by decide
  have hdescent : baseEnd_6222016 < baseStart_6222016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222030 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_6222030 : Nat := 118140960795 + 6222030 * 2 ^ 59
def prefixEnd_6222030 : Nat := 4983230072969 + 3 ^ 40 * 6222030 * 2
def baseEnd_6222030 : Nat := 3194892036694396512710411

theorem tailTrace_6222030 : CollatzResearch.WordTrace tailWord_6222030 prefixEnd_6222030 3194892036694396512710411 := by
  unfold tailWord_6222030
  simp only [CollatzResearch.WordTrace]
  refine ⟨28367009706081927871020943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151290718432436948645445029 28367009706081927871020943)
  ·
    refine ⟨42550514559122891806531415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28367009706081927871020943 42550514559122891806531415)
    ·
      refine ⟨63825771838684337709797123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42550514559122891806531415 63825771838684337709797123)
      ·
        refine ⟨95738657758026506564695685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63825771838684337709797123 95738657758026506564695685)
        ·
          refine ⟨17950998329629969980880441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95738657758026506564695685 17950998329629969980880441)
          ·
            refine ⟨13463248747222477485660331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17950998329629969980880441 13463248747222477485660331)
            ·
              refine ⟨20194873120833716228490497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13463248747222477485660331 20194873120833716228490497)
              ·
                refine ⟨15146154840625287171367873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20194873120833716228490497 15146154840625287171367873)
                ·
                  refine ⟨11359616130468965378525905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15146154840625287171367873 11359616130468965378525905)
                  ·
                    refine ⟨8519712097851724033894429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11359616130468965378525905 8519712097851724033894429)
                    ·
                      refine ⟨3194892036694396512710411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519712097851724033894429 3194892036694396512710411)
                      ·
                        rfl

theorem cell23_6222030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_6222030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222030 prefixEnd_6222030 := by exact prefixLift 6222030
  have htrace : WordTrace (prefixWord ++ tailWord_6222030) baseStart_6222030 baseEnd_6222030 := by
    simpa [prefixWord, tailWord_6222030, baseEnd_6222030] using wordTrace_append hprefix tailTrace_6222030
  have hstable : (prefixWord ++ tailWord_6222030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222030).length < 2 ^ (prefixWord ++ tailWord_6222030).sum := by decide
  have hdescent : baseEnd_6222030 < baseStart_6222030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222037 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_6222037 : Nat := 118140960795 + 6222037 * 2 ^ 59
def prefixEnd_6222037 : Nat := 4983230072969 + 3 ^ 40 * 6222037 * 2
def baseEnd_6222037 : Nat := 1064965210352992661774293

theorem tailTrace_6222037 : CollatzResearch.WordTrace tailWord_6222037 prefixEnd_6222037 1064965210352992661774293 := by
  unfold tailWord_6222037
  simp only [CollatzResearch.WordTrace]
  refine ⟨226936332959630063163672365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151290888639753375442448243 226936332959630063163672365)
  ·
    refine ⟨85101124859861273686377137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226936332959630063163672365 85101124859861273686377137)
    ·
      refine ⟨63825843644895955264782853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85101124859861273686377137 63825843644895955264782853)
      ·
        refine ⟨11967345683417991612146785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63825843644895955264782853 11967345683417991612146785)
        ·
          refine ⟨8975509262563493709110089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11967345683417991612146785 8975509262563493709110089)
          ·
            refine ⟨6731631946922620281832567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8975509262563493709110089 6731631946922620281832567)
            ·
              refine ⟨10097447920383930422748851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731631946922620281832567 10097447920383930422748851)
              ·
                refine ⟨15146171880575895634123277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10097447920383930422748851 15146171880575895634123277)
                ·
                  refine ⟨5679814455215960862796229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15146171880575895634123277 5679814455215960862796229)
                  ·
                    refine ⟨1064965210352992661774293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5679814455215960862796229 1064965210352992661774293)
                    ·
                      rfl

theorem cell23_6222037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_6222037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222037 prefixEnd_6222037 := by exact prefixLift 6222037
  have htrace : WordTrace (prefixWord ++ tailWord_6222037) baseStart_6222037 baseEnd_6222037 := by
    simpa [prefixWord, tailWord_6222037, baseEnd_6222037] using wordTrace_append hprefix tailTrace_6222037
  have hstable : (prefixWord ++ tailWord_6222037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222037).length < 2 ^ (prefixWord ++ tailWord_6222037).sum := by decide
  have hdescent : baseEnd_6222037 < baseStart_6222037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222063 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 3, 5]
def baseStart_6222063 : Nat := 118140960795 + 6222063 * 2 ^ 59
def prefixEnd_6222063 : Nat := 4983230072969 + 3 ^ 40 * 6222063 * 2
def baseEnd_6222063 : Nat := 1064969660518664961199253

theorem tailTrace_6222063 : CollatzResearch.WordTrace tailWord_6222063 prefixEnd_6222063 1064969660518664961199253 := by
  unfold tailWord_6222063
  simp only [CollatzResearch.WordTrace]
  refine ⟨226937281257535869604118843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151291520838357246402745895 226937281257535869604118843)
  ·
    refine ⟨340405921886303804406178265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226937281257535869604118843 340405921886303804406178265)
    ·
      refine ⟨255304441414727853304633699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340405921886303804406178265 255304441414727853304633699)
      ·
        refine ⟨382956662122091779956950549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255304441414727853304633699 382956662122091779956950549)
        ·
          refine ⟨17951093536973052185482057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382956662122091779956950549 17951093536973052185482057)
          ·
            refine ⟨13463320152729789139111543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17951093536973052185482057 13463320152729789139111543)
            ·
              refine ⟨20194980229094683708667315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13463320152729789139111543 20194980229094683708667315)
              ·
                refine ⟨30292470343642025563000973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20194980229094683708667315 30292470343642025563000973)
                ·
                  refine ⟨11359676378865759586125365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30292470343642025563000973 11359676378865759586125365)
                  ·
                    refine ⟨1064969660518664961199253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11359676378865759586125365 1064969660518664961199253)
                    ·
                      rfl

theorem cell23_6222063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_6222063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222063 prefixEnd_6222063 := by exact prefixLift 6222063
  have htrace : WordTrace (prefixWord ++ tailWord_6222063) baseStart_6222063 baseEnd_6222063 := by
    simpa [prefixWord, tailWord_6222063, baseEnd_6222063] using wordTrace_append hprefix tailTrace_6222063
  have hstable : (prefixWord ++ tailWord_6222063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222063).length < 2 ^ (prefixWord ++ tailWord_6222063).sum := by decide
  have hdescent : baseEnd_6222063 < baseStart_6222063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222070 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6222070 : Nat := 118140960795 + 6222070 * 2 ^ 59
def prefixEnd_6222070 : Nat := 4983230072969 + 3 ^ 40 * 6222070 * 2
def baseEnd_6222070 : Nat := 3194912575920576356210227

theorem tailTrace_6222070 : CollatzResearch.WordTrace tailWord_6222070 prefixEnd_6222070 3194912575920576356210227 := by
  unfold tailWord_6222070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14183596035531906862476479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151291691045673673199749109 14183596035531906862476479)
  ·
    refine ⟨21275394053297860293714719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14183596035531906862476479 21275394053297860293714719)
    ·
      refine ⟨31913091079946790440572079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21275394053297860293714719 31913091079946790440572079)
      ·
        refine ⟨47869636619920185660858119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31913091079946790440572079 47869636619920185660858119)
        ·
          refine ⟨71804454929880278491287179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47869636619920185660858119 71804454929880278491287179)
          ·
            refine ⟨107706682394820417736930769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71804454929880278491287179 107706682394820417736930769)
            ·
              refine ⟨80780011796115313302698077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107706682394820417736930769 80780011796115313302698077)
              ·
                refine ⟨30292504423543242488511779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80780011796115313302698077 30292504423543242488511779)
                ·
                  refine ⟨45438756635314863732767669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30292504423543242488511779 45438756635314863732767669)
                  ·
                    refine ⟨4259883434560768474946969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45438756635314863732767669 4259883434560768474946969)
                    ·
                      refine ⟨3194912575920576356210227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259883434560768474946969 3194912575920576356210227)
                      ·
                        rfl

theorem cell23_6222070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6222070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222070 prefixEnd_6222070 := by exact prefixLift 6222070
  have htrace : WordTrace (prefixWord ++ tailWord_6222070) baseStart_6222070 baseEnd_6222070 := by
    simpa [prefixWord, tailWord_6222070, baseEnd_6222070] using wordTrace_append hprefix tailTrace_6222070
  have hstable : (prefixWord ++ tailWord_6222070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222070).length < 2 ^ (prefixWord ++ tailWord_6222070).sum := by decide
  have hdescent : baseEnd_6222070 < baseStart_6222070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222113 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6222113 : Nat := 118140960795 + 6222113 * 2 ^ 59
def prefixEnd_6222113 : Nat := 4983230072969 + 3 ^ 40 * 6222113 * 2
def baseEnd_6222113 : Nat := 3194934655588719687972529

theorem tailTrace_6222113 : CollatzResearch.WordTrace tailWord_6222113 prefixEnd_6222113 3194934655588719687972529 := by
  unfold tailWord_6222113
  simp only [CollatzResearch.WordTrace]
  refine ⟨226939104907354728143438993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151292736604903152095625995 226939104907354728143438993)
  ·
    refine ⟨170204328680516046107579245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226939104907354728143438993 170204328680516046107579245)
    ·
      refine ⟨63826623255193517290342217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170204328680516046107579245 63826623255193517290342217)
      ·
        refine ⟨47869967441395137967756663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63826623255193517290342217 47869967441395137967756663)
        ·
          refine ⟨71804951162092706951634995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47869967441395137967756663 71804951162092706951634995)
          ·
            refine ⟨107707426743139060427452493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71804951162092706951634995 107707426743139060427452493)
            ·
              refine ⟨40390285028677147660294685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107707426743139060427452493 40390285028677147660294685)
              ·
                refine ⟨15146356885753930372610507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40390285028677147660294685 15146356885753930372610507)
                ·
                  refine ⟨22719535328630895558915761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15146356885753930372610507 22719535328630895558915761)
                  ·
                    refine ⟨17039651496473171669186821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22719535328630895558915761 17039651496473171669186821)
                    ·
                      refine ⟨3194934655588719687972529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17039651496473171669186821 3194934655588719687972529)
                      ·
                        rfl

theorem cell23_6222113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6222113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222113 prefixEnd_6222113 := by exact prefixLift 6222113
  have htrace : WordTrace (prefixWord ++ tailWord_6222113) baseStart_6222113 baseEnd_6222113 := by
    simpa [prefixWord, tailWord_6222113, baseEnd_6222113] using wordTrace_append hprefix tailTrace_6222113
  have hstable : (prefixWord ++ tailWord_6222113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222113).length < 2 ^ (prefixWord ++ tailWord_6222113).sum := by decide
  have hdescent : baseEnd_6222113 < baseStart_6222113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222137 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6222137 : Nat := 118140960795 + 6222137 * 2 ^ 59
def prefixEnd_6222137 : Nat := 4983230072969 + 3 ^ 40 * 6222137 * 2
def baseEnd_6222137 : Nat := 3194946979124427594072419

theorem tailTrace_6222137 : CollatzResearch.WordTrace tailWord_6222137 prefixEnd_6222137 3194946979124427594072419 := by
  unfold tailWord_6222137
  simp only [CollatzResearch.WordTrace]
  refine ⟨226939980259267780242312665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151293320172845186828208443 226939980259267780242312665)
  ·
    refine ⟨170204985194450835181734499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226939980259267780242312665 170204985194450835181734499)
    ·
      refine ⟨255307477791676252772601749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170204985194450835181734499 255307477791676252772601749)
      ·
        refine ⟨11967538021484824348715707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255307477791676252772601749 11967538021484824348715707)
        ·
          refine ⟨17951307032227236523073561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11967538021484824348715707 17951307032227236523073561)
          ·
            refine ⟨13463480274170427392305171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17951307032227236523073561 13463480274170427392305171)
            ·
              refine ⟨20195220411255641088457757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13463480274170427392305171 20195220411255641088457757)
              ·
                refine ⟨7573207654220865408171659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20195220411255641088457757 7573207654220865408171659)
                ·
                  refine ⟨11359811481331298112257489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7573207654220865408171659 11359811481331298112257489)
                  ·
                    refine ⟨8519858610998473584193117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11359811481331298112257489 8519858610998473584193117)
                    ·
                      refine ⟨3194946979124427594072419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519858610998473584193117 3194946979124427594072419)
                      ·
                        rfl

theorem cell23_6222137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6222137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222137 prefixEnd_6222137 := by exact prefixLift 6222137
  have htrace : WordTrace (prefixWord ++ tailWord_6222137) baseStart_6222137 baseEnd_6222137 := by
    simpa [prefixWord, tailWord_6222137, baseEnd_6222137] using wordTrace_append hprefix tailTrace_6222137
  have hstable : (prefixWord ++ tailWord_6222137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222137).length < 2 ^ (prefixWord ++ tailWord_6222137).sum := by decide
  have hdescent : baseEnd_6222137 < baseStart_6222137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222193 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_6222193 : Nat := 118140960795 + 6222193 * 2 ^ 59
def prefixEnd_6222193 : Nat := 4983230072969 + 3 ^ 40 * 6222193 * 2
def baseEnd_6222193 : Nat := 3194975734041079374972161

theorem tailTrace_6222193 : CollatzResearch.WordTrace tailWord_6222193 prefixEnd_6222193 3194975734041079374972161 := by
  unfold tailWord_6222193
  simp only [CollatzResearch.WordTrace]
  refine ⟨226942022747064901806351233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151294681831376601204234155 226942022747064901806351233)
  ·
    refine ⟨170206517060298676354763425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226942022747064901806351233 170206517060298676354763425)
    ·
      refine ⟨127654887795224007266072569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170206517060298676354763425 127654887795224007266072569)
      ·
        refine ⟨95741165846418005449554427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127654887795224007266072569 95741165846418005449554427)
        ·
          refine ⟨143611748769627008174331641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95741165846418005449554427 143611748769627008174331641)
          ·
            refine ⟨107708811577220256130748731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143611748769627008174331641 107708811577220256130748731)
            ·
              refine ⟨161563217365830384196123097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107708811577220256130748731 161563217365830384196123097)
              ·
                refine ⟨121172413024372788147092323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161563217365830384196123097 121172413024372788147092323)
                ·
                  refine ⟨181758619536559182220638485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121172413024372788147092323 181758619536559182220638485)
                  ·
                    refine ⟨8519935290776211666592429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181758619536559182220638485 8519935290776211666592429)
                    ·
                      refine ⟨3194975734041079374972161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519935290776211666592429 3194975734041079374972161)
                      ·
                        rfl

theorem cell23_6222193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_6222193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222193 prefixEnd_6222193 := by exact prefixLift 6222193
  have htrace : WordTrace (prefixWord ++ tailWord_6222193) baseStart_6222193 baseEnd_6222193 := by
    simpa [prefixWord, tailWord_6222193, baseEnd_6222193] using wordTrace_append hprefix tailTrace_6222193
  have hstable : (prefixWord ++ tailWord_6222193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222193).length < 2 ^ (prefixWord ++ tailWord_6222193).sum := by decide
  have hdescent : baseEnd_6222193 < baseStart_6222193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222218 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6222218 : Nat := 118140960795 + 6222218 * 2 ^ 59
def prefixEnd_6222218 : Nat := 4983230072969 + 3 ^ 40 * 6222218 * 2
def baseEnd_6222218 : Nat := 3194988571057441777159547

theorem tailTrace_6222218 : CollatzResearch.WordTrace tailWord_6222218 prefixEnd_6222218 3194988571057441777159547 := by
  unfold tailWord_6222218
  simp only [CollatzResearch.WordTrace]
  refine ⟨56735733642993582769002827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151295289714649554050674205 56735733642993582769002827)
  ·
    refine ⟨85103600464490374153504241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56735733642993582769002827 85103600464490374153504241)
    ·
      refine ⟨63827700348367780615128181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85103600464490374153504241 63827700348367780615128181)
      ·
        refine ⟨5983846907659479432668267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63827700348367780615128181 5983846907659479432668267)
        ·
          refine ⟨8975770361489219149002401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983846907659479432668267 8975770361489219149002401)
          ·
            refine ⟨6731827771116914361751801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8975770361489219149002401 6731827771116914361751801)
            ·
              refine ⟨5048870828337685771313851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6731827771116914361751801 5048870828337685771313851)
              ·
                refine ⟨7573306242506528656970777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5048870828337685771313851 7573306242506528656970777)
                ·
                  refine ⟨5679979681879896492728083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7573306242506528656970777 5679979681879896492728083)
                  ·
                    refine ⟨8519969522819844739092125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5679979681879896492728083 8519969522819844739092125)
                    ·
                      refine ⟨3194988571057441777159547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8519969522819844739092125 3194988571057441777159547)
                      ·
                        rfl

theorem cell23_6222218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6222218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222218 prefixEnd_6222218 := by exact prefixLift 6222218
  have htrace : WordTrace (prefixWord ++ tailWord_6222218) baseStart_6222218 baseEnd_6222218 := by
    simpa [prefixWord, tailWord_6222218, baseEnd_6222218] using wordTrace_append hprefix tailTrace_6222218
  have hstable : (prefixWord ++ tailWord_6222218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222218).length < 2 ^ (prefixWord ++ tailWord_6222218).sum := by decide
  have hdescent : baseEnd_6222218 < baseStart_6222218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222228 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6222228 : Nat := 118140960795 + 6222228 * 2 ^ 59
def prefixEnd_6222228 : Nat := 4983230072969 + 3 ^ 40 * 6222228 * 2
def baseEnd_6222228 : Nat := 3194993705863986738034501

theorem tailTrace_6222228 : CollatzResearch.WordTrace tailWord_6222228 prefixEnd_6222228 3194993705863986738034501 := by
  unfold tailWord_6222228
  simp only [CollatzResearch.WordTrace]
  refine ⟨113471649650969051391937669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151295532867958735189250225 113471649650969051391937669)
  ·
    refine ⟨21275934309556697135988313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113471649650969051391937669 21275934309556697135988313)
    ·
      refine ⟨15956950732167522851991235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21275934309556697135988313 15956950732167522851991235)
      ·
        refine ⟨23935426098251284277986853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15956950732167522851991235 23935426098251284277986853)
        ·
          refine ⟨4487892393422115802122535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23935426098251284277986853 4487892393422115802122535)
          ·
            refine ⟨6731838590133173703183803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487892393422115802122535 6731838590133173703183803)
            ·
              refine ⟨10097757885199760554775705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731838590133173703183803 10097757885199760554775705)
              ·
                refine ⟨7573318413899820416081779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10097757885199760554775705 7573318413899820416081779)
                ·
                  refine ⟨11359977620849730624122669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7573318413899820416081779 11359977620849730624122669)
                  ·
                    refine ⟨4259991607818648984046001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11359977620849730624122669 4259991607818648984046001)
                    ·
                      refine ⟨3194993705863986738034501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4259991607818648984046001 3194993705863986738034501)
                      ·
                        rfl

theorem cell23_6222228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6222228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222228 prefixEnd_6222228 := by exact prefixLift 6222228
  have htrace : WordTrace (prefixWord ++ tailWord_6222228) baseStart_6222228 baseEnd_6222228 := by
    simpa [prefixWord, tailWord_6222228, baseEnd_6222228] using wordTrace_append hprefix tailTrace_6222228
  have hstable : (prefixWord ++ tailWord_6222228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222228).length < 2 ^ (prefixWord ++ tailWord_6222228).sum := by decide
  have hdescent : baseEnd_6222228 < baseStart_6222228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222270 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_6222270 : Nat := 118140960795 + 6222270 * 2 ^ 59
def prefixEnd_6222270 : Nat := 4983230072969 + 3 ^ 40 * 6222270 * 2
def baseEnd_6222270 : Nat := 3195015272051475573709307

theorem tailTrace_6222270 : CollatzResearch.WordTrace tailWord_6222270 prefixEnd_6222270 3195015272051475573709307 := by
  unfold tailWord_6222270
  simp only [CollatzResearch.WordTrace]
  refine ⟨28368103895973242994613033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151296554111857295971269509 28368103895973242994613033)
  ·
    refine ⟨21276077921979932245959775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28368103895973242994613033 21276077921979932245959775)
    ·
      refine ⟨31914116882969898368939663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21276077921979932245959775 31914116882969898368939663)
      ·
        refine ⟨47871175324454847553409495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31914116882969898368939663 47871175324454847553409495)
        ·
          refine ⟨71806762986682271330114243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47871175324454847553409495 71806762986682271330114243)
          ·
            refine ⟨107710144480023406995171365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71806762986682271330114243 107710144480023406995171365)
            ·
              refine ⟨20195652090004388811594631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107710144480023406995171365 20195652090004388811594631)
              ·
                refine ⟨30293478135006583217391947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20195652090004388811594631 30293478135006583217391947)
                ·
                  refine ⟨45440217202509874826087921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30293478135006583217391947 45440217202509874826087921)
                  ·
                    refine ⟨34080162901882406119565941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45440217202509874826087921 34080162901882406119565941)
                    ·
                      refine ⟨3195015272051475573709307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34080162901882406119565941 3195015272051475573709307)
                      ·
                        rfl

theorem cell23_6222270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_6222270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222270 prefixEnd_6222270 := by exact prefixLift 6222270
  have htrace : WordTrace (prefixWord ++ tailWord_6222270) baseStart_6222270 baseEnd_6222270 := by
    simpa [prefixWord, tailWord_6222270, baseEnd_6222270] using wordTrace_append hprefix tailTrace_6222270
  have hstable : (prefixWord ++ tailWord_6222270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222270).length < 2 ^ (prefixWord ++ tailWord_6222270).sum := by decide
  have hdescent : baseEnd_6222270 < baseStart_6222270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222323 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_6222323 : Nat := 118140960795 + 6222323 * 2 ^ 59
def prefixEnd_6222323 : Nat := 4983230072969 + 3 ^ 40 * 6222323 * 2
def baseEnd_6222323 : Nat := 3195042486526163866346563

theorem tailTrace_6222323 : CollatzResearch.WordTrace tailWord_6222323 prefixEnd_6222323 3195042486526163866346563 := by
  unfold tailWord_6222323
  simp only [CollatzResearch.WordTrace]
  refine ⟨226946764236593934008583623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151297842824395956005722415 226946764236593934008583623)
  ·
    refine ⟨340420146354890901012875435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226946764236593934008583623 340420146354890901012875435)
    ·
      refine ⟨510630219532336351519313153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340420146354890901012875435 510630219532336351519313153)
      ·
        refine ⟨382972664649252263639484865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510630219532336351519313153 382972664649252263639484865)
        ·
          refine ⟨287229498486939197729613649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382972664649252263639484865 287229498486939197729613649)
          ·
            refine ⟨215422123865204398297210237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287229498486939197729613649 215422123865204398297210237)
            ·
              refine ⟨80783296449451649361453839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215422123865204398297210237 80783296449451649361453839)
              ·
                refine ⟨121174944674177474042180759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80783296449451649361453839 121174944674177474042180759)
                ·
                  refine ⟨181762417011266211063271139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121174944674177474042180759 181762417011266211063271139)
                  ·
                    refine ⟨272643625516899316594906709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 181762417011266211063271139 272643625516899316594906709)
                    ·
                      refine ⟨3195042486526163866346563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 272643625516899316594906709 3195042486526163866346563)
                      ·
                        rfl

theorem cell23_6222323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_6222323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222323 prefixEnd_6222323 := by exact prefixLift 6222323
  have htrace : WordTrace (prefixWord ++ tailWord_6222323) baseStart_6222323 baseEnd_6222323 := by
    simpa [prefixWord, tailWord_6222323, baseEnd_6222323] using wordTrace_append hprefix tailTrace_6222323
  have hstable : (prefixWord ++ tailWord_6222323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222323).length < 2 ^ (prefixWord ++ tailWord_6222323).sum := by decide
  have hdescent : baseEnd_6222323 < baseStart_6222323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222357 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_6222357 : Nat := 118140960795 + 6222357 * 2 ^ 59
def prefixEnd_6222357 : Nat := 4983230072969 + 3 ^ 40 * 6222357 * 2
def baseEnd_6222357 : Nat := 3195059944868416733321407

theorem tailTrace_6222357 : CollatzResearch.WordTrace tailWord_6222357 prefixEnd_6222357 3195059944868416733321407 := by
  unfold tailWord_6222357
  simp only [CollatzResearch.WordTrace]
  refine ⟨226948004318470757815321325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151298669545647171876880883 226948004318470757815321325)
  ·
    refine ⟨85105501619426534180745497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226948004318470757815321325 85105501619426534180745497)
    ·
      refine ⟨63829126214569900635559123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85105501619426534180745497 63829126214569900635559123)
      ·
        refine ⟨95743689321854850953338685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63829126214569900635559123 95743689321854850953338685)
        ·
          refine ⟨35903883495695569107502007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95743689321854850953338685 35903883495695569107502007)
          ·
            refine ⟨53855825243543353661253011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35903883495695569107502007 53855825243543353661253011)
            ·
              refine ⟨80783737865315030491879517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53855825243543353661253011 80783737865315030491879517)
              ·
                refine ⟨30293901699493136434454819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80783737865315030491879517 30293901699493136434454819)
                ·
                  refine ⟨45440852549239704651682229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30293901699493136434454819 45440852549239704651682229)
                  ·
                    refine ⟨4260079926491222311095209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45440852549239704651682229 4260079926491222311095209)
                    ·
                      refine ⟨3195059944868416733321407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260079926491222311095209 3195059944868416733321407)
                      ·
                        rfl

theorem cell23_6222357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_6222357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222357 prefixEnd_6222357 := by exact prefixLift 6222357
  have htrace : WordTrace (prefixWord ++ tailWord_6222357) baseStart_6222357 baseEnd_6222357 := by
    simpa [prefixWord, tailWord_6222357, baseEnd_6222357] using wordTrace_append hprefix tailTrace_6222357
  have hstable : (prefixWord ++ tailWord_6222357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222357).length < 2 ^ (prefixWord ++ tailWord_6222357).sum := by decide
  have hdescent : baseEnd_6222357 < baseStart_6222357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222375 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 1, 4]
def baseStart_6222375 : Nat := 118140960795 + 6222375 * 2 ^ 59
def prefixEnd_6222375 : Nat := 4983230072969 + 3 ^ 40 * 6222375 * 2
def baseEnd_6222375 : Nat := 1065023062506732554298775

theorem tailTrace_6222375 : CollatzResearch.WordTrace tailWord_6222375 prefixEnd_6222375 1065023062506732554298775 := by
  unfold tailWord_6222375
  simp only [CollatzResearch.WordTrace]
  refine ⟨226948660832405546889476579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151299107221603697926317719 226948660832405546889476579)
  ·
    refine ⟨340422991248608320334214869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226948660832405546889476579 340422991248608320334214869)
    ·
      refine ⟨7978663857389257507833161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 340422991248608320334214869 7978663857389257507833161)
      ·
        refine ⟨5983997893041943130874871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7978663857389257507833161 5983997893041943130874871)
        ·
          refine ⟨8975996839562914696312307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5983997893041943130874871 8975996839562914696312307)
          ·
            refine ⟨13463995259344372044468461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8975996839562914696312307 13463995259344372044468461)
            ·
              refine ⟨5048998222254139516675673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13463995259344372044468461 5048998222254139516675673)
              ·
                refine ⟨3786748666690604637506755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5048998222254139516675673 3786748666690604637506755)
                ·
                  refine ⟨5680123000035906956260133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786748666690604637506755 5680123000035906956260133)
                  ·
                    refine ⟨1065023062506732554298775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680123000035906956260133 1065023062506732554298775)
                    ·
                      rfl

theorem cell23_6222375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_6222375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222375 prefixEnd_6222375 := by exact prefixLift 6222375
  have htrace : WordTrace (prefixWord ++ tailWord_6222375) baseStart_6222375 baseEnd_6222375 := by
    simpa [prefixWord, tailWord_6222375, baseEnd_6222375] using wordTrace_append hprefix tailTrace_6222375
  have hstable : (prefixWord ++ tailWord_6222375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222375).length < 2 ^ (prefixWord ++ tailWord_6222375).sum := by decide
  have hdescent : baseEnd_6222375 < baseStart_6222375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222388 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 6]
def baseStart_6222388 : Nat := 118140960795 + 6222388 * 2 ^ 59
def prefixEnd_6222388 : Nat := 4983230072969 + 3 ^ 40 * 6222388 * 2
def baseEnd_6222388 : Nat := 355008429196522901337085

theorem tailTrace_6222388 : CollatzResearch.WordTrace tailWord_6222388 prefixEnd_6222388 355008429196522901337085 := by
  unfold tailWord_6222388
  simp only [CollatzResearch.WordTrace]
  refine ⟨113474567490679225054849909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151299423320905633406466545 113474567490679225054849909)
  ·
    refine ⟨10638240702251177348892179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113474567490679225054849909 10638240702251177348892179)
    ·
      refine ⟨15957361053376766023338269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10638240702251177348892179 15957361053376766023338269)
      ·
        refine ⟨5984010395016287258751851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15957361053376766023338269 5984010395016287258751851)
        ·
          refine ⟨8976015592524430888127777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984010395016287258751851 8976015592524430888127777)
          ·
            refine ⟨6732011694393323166095833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8976015592524430888127777 6732011694393323166095833)
            ·
              refine ⟨5049008770794992374571875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6732011694393323166095833 5049008770794992374571875)
              ·
                refine ⟨7573513156192488561857813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5049008770794992374571875 7573513156192488561857813)
                ·
                  refine ⟨355008429196522901337085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7573513156192488561857813 355008429196522901337085)
                  ·
                    rfl

theorem cell23_6222388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_6222388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222388 prefixEnd_6222388 := by exact prefixLift 6222388
  have htrace : WordTrace (prefixWord ++ tailWord_6222388) baseStart_6222388 baseEnd_6222388 := by
    simpa [prefixWord, tailWord_6222388, baseEnd_6222388] using wordTrace_append hprefix tailTrace_6222388
  have hstable : (prefixWord ++ tailWord_6222388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222388).length < 2 ^ (prefixWord ++ tailWord_6222388).sum := by decide
  have hdescent : baseEnd_6222388 < baseStart_6222388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222400 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_6222400 : Nat := 118140960795 + 6222400 * 2 ^ 59
def prefixEnd_6222400 : Nat := 4983230072969 + 3 ^ 40 * 6222400 * 2
def baseEnd_6222400 : Nat := 3195082024536560065083709

theorem tailTrace_6222400 : CollatzResearch.WordTrace tailWord_6222400 prefixEnd_6222400 3195082024536560065083709 := by
  unfold tailWord_6222400
  simp only [CollatzResearch.WordTrace]
  refine ⟨113474786328657488079568327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151299715104876650772757769 113474786328657488079568327)
  ·
    refine ⟨170212179492986232119352491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113474786328657488079568327 170212179492986232119352491)
    ·
      refine ⟨255318269239479348179028737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170212179492986232119352491 255318269239479348179028737)
      ·
        refine ⟨191488701929609511134271553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255318269239479348179028737 191488701929609511134271553)
        ·
          refine ⟨143616526447207133350703665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191488701929609511134271553 143616526447207133350703665)
          ·
            refine ⟨107712394835405350013027749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143616526447207133350703665 107712394835405350013027749)
            ·
              refine ⟨20196074031638503127442703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107712394835405350013027749 20196074031638503127442703)
              ·
                refine ⟨30294111047457754691164055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20196074031638503127442703 30294111047457754691164055)
                ·
                  refine ⟨45441166571186632036746083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30294111047457754691164055 45441166571186632036746083)
                  ·
                    refine ⟨68161749856779948055119125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45441166571186632036746083 68161749856779948055119125)
                    ·
                      refine ⟨3195082024536560065083709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68161749856779948055119125 3195082024536560065083709)
                      ·
                        rfl

theorem cell23_6222400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_6222400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222400 prefixEnd_6222400 := by exact prefixLift 6222400
  have htrace : WordTrace (prefixWord ++ tailWord_6222400) baseStart_6222400 baseEnd_6222400 := by
    simpa [prefixWord, tailWord_6222400, baseEnd_6222400] using wordTrace_append hprefix tailTrace_6222400
  have hstable : (prefixWord ++ tailWord_6222400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222400).length < 2 ^ (prefixWord ++ tailWord_6222400).sum := by decide
  have hdescent : baseEnd_6222400 < baseStart_6222400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222410 : List Nat := [3, 1, 2, 1, 1, 4, 2, 9]
def baseStart_6222410 : Nat := 118140960795 + 6222410 * 2 ^ 59
def prefixEnd_6222410 : Nat := 4983230072969 + 3 ^ 40 * 6222410 * 2
def baseEnd_6222410 : Nat := 118336561457152037998469

theorem tailTrace_6222410 : CollatzResearch.WordTrace tailWord_6222410 prefixEnd_6222410 118336561457152037998469 := by
  unfold tailWord_6222410
  simp only [CollatzResearch.WordTrace]
  refine ⟨56737484346819686966750171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151299958258185831911333789 56737484346819686966750171)
  ·
    refine ⟨85106226520229530450125257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56737484346819686966750171 85106226520229530450125257)
    ·
      refine ⟨63829669890172147837593943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85106226520229530450125257 63829669890172147837593943)
      ·
        refine ⟨95744504835258221756390915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63829669890172147837593943 95744504835258221756390915)
        ·
          refine ⟨143616757252887332634586373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95744504835258221756390915 143616757252887332634586373)
          ·
            refine ⟨26928141984916374868984945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143616757252887332634586373 26928141984916374868984945)
            ·
              refine ⟨20196106488687281151738709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26928141984916374868984945 20196106488687281151738709)
              ·
                refine ⟨118336561457152037998469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20196106488687281151738709 118336561457152037998469)
                ·
                  rfl

theorem cell23_6222410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_6222410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222410 prefixEnd_6222410 := by exact prefixLift 6222410
  have htrace : WordTrace (prefixWord ++ tailWord_6222410) baseStart_6222410 baseEnd_6222410 := by
    simpa [prefixWord, tailWord_6222410, baseEnd_6222410] using wordTrace_append hprefix tailTrace_6222410
  have hstable : (prefixWord ++ tailWord_6222410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222410).length < 2 ^ (prefixWord ++ tailWord_6222410).sum := by decide
  have hdescent : baseEnd_6222410 < baseStart_6222410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222417 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_6222417 : Nat := 118140960795 + 6222417 * 2 ^ 59
def prefixEnd_6222417 : Nat := 4983230072969 + 3 ^ 40 * 6222417 * 2
def baseEnd_6222417 : Nat := 3195090753707686498571131

theorem tailTrace_6222417 : CollatzResearch.WordTrace tailWord_6222417 prefixEnd_6222417 3195090753707686498571131 := by
  unfold tailWord_6222417
  simp only [CollatzResearch.WordTrace]
  refine ⟨226950192698253388062505505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151300128465502258708337003 226950192698253388062505505)
  ·
    refine ⟨170212644523690041046879129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226950192698253388062505505 170212644523690041046879129)
    ·
      refine ⟨127659483392767530785159347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170212644523690041046879129 127659483392767530785159347)
      ·
        refine ⟨191489225089151296177739021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127659483392767530785159347 191489225089151296177739021)
        ·
          refine ⟨71808459408431736066652133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191489225089151296177739021 71808459408431736066652133)
          ·
            refine ⟨13464086139080950512497275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71808459408431736066652133 13464086139080950512497275)
            ·
              refine ⟨20196129208621425768745913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464086139080950512497275 20196129208621425768745913)
              ·
                refine ⟨15147096906466069326559435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20196129208621425768745913 15147096906466069326559435)
                ·
                  refine ⟨22720645359699103989839153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15147096906466069326559435 22720645359699103989839153)
                  ·
                    refine ⟨17040484019774327992379365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22720645359699103989839153 17040484019774327992379365)
                    ·
                      refine ⟨3195090753707686498571131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17040484019774327992379365 3195090753707686498571131)
                      ·
                        rfl

theorem cell23_6222417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_6222417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222417 prefixEnd_6222417 := by exact prefixLift 6222417
  have htrace : WordTrace (prefixWord ++ tailWord_6222417) baseStart_6222417 baseEnd_6222417 := by
    simpa [prefixWord, tailWord_6222417, baseEnd_6222417] using wordTrace_append hprefix tailTrace_6222417
  have hstable : (prefixWord ++ tailWord_6222417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222417).length < 2 ^ (prefixWord ++ tailWord_6222417).sum := by decide
  have hdescent : baseEnd_6222417 < baseStart_6222417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222464 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2]
def baseStart_6222464 : Nat := 118140960795 + 6222464 * 2 ^ 59
def prefixEnd_6222464 : Nat := 4983230072969 + 3 ^ 40 * 6222464 * 2
def baseEnd_6222464 : Nat := 3195114887298447814683415

theorem tailTrace_6222464 : CollatzResearch.WordTrace tailWord_6222464 prefixEnd_6222464 3195114887298447814683415 := by
  unfold tailWord_6222464
  simp only [CollatzResearch.WordTrace]
  refine ⟨113475953464541557544733223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151301271286055410059644297 113475953464541557544733223)
  ·
    refine ⟨170213930196812336317099835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113475953464541557544733223 170213930196812336317099835)
    ·
      refine ⟨255320895295218504475649753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170213930196812336317099835 255320895295218504475649753)
      ·
        refine ⟨191490671471413878356737315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255320895295218504475649753 191490671471413878356737315)
        ·
          refine ⟨287236007207120817535105973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191490671471413878356737315 287236007207120817535105973)
          ·
            refine ⟨26928375675667576643916185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287236007207120817535105973 26928375675667576643916185)
            ·
              refine ⟨20196281756750682482937139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26928375675667576643916185 20196281756750682482937139)
              ·
                refine ⟨30294422635126023724405709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20196281756750682482937139 30294422635126023724405709)
                ·
                  refine ⟨11360408488172258896652141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30294422635126023724405709 11360408488172258896652141)
                  ·
                    refine ⟨4260153183064597086244553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11360408488172258896652141 4260153183064597086244553)
                    ·
                      refine ⟨3195114887298447814683415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260153183064597086244553 3195114887298447814683415)
                      ·
                        rfl

theorem cell23_6222464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_6222464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222464 prefixEnd_6222464 := by exact prefixLift 6222464
  have htrace : WordTrace (prefixWord ++ tailWord_6222464) baseStart_6222464 baseEnd_6222464 := by
    simpa [prefixWord, tailWord_6222464, baseEnd_6222464] using wordTrace_append hprefix tailTrace_6222464
  have hstable : (prefixWord ++ tailWord_6222464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222464).length < 2 ^ (prefixWord ++ tailWord_6222464).sum := by decide
  have hdescent : baseEnd_6222464 < baseStart_6222464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222511 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 1, 4, 2]
def baseStart_6222511 : Nat := 118140960795 + 6222511 * 2 ^ 59
def prefixEnd_6222511 : Nat := 4983230072969 + 3 ^ 40 * 6222511 * 2
def baseEnd_6222511 : Nat := 3195139020889209130795699

theorem tailTrace_6222511 : CollatzResearch.WordTrace tailWord_6222511 prefixEnd_6222511 3195139020889209130795699 := by
  unfold tailWord_6222511
  simp only [CollatzResearch.WordTrace]
  refine ⟨226953621159912842116427387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151302414106608561410951591 226953621159912842116427387)
  ·
    refine ⟨340430431739869263174641081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226953621159912842116427387 340430431739869263174641081)
    ·
      refine ⟨255322823804901947380980811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 340430431739869263174641081 255322823804901947380980811)
      ·
        refine ⟨382984235707352921071471217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255322823804901947380980811 382984235707352921071471217)
        ·
          refine ⟨287238176780514690803603413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382984235707352921071471217 287238176780514690803603413)
          ·
            refine ⟨6732144768293313065709455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 287238176780514690803603413 6732144768293313065709455)
            ·
              refine ⟨10098217152439969598564183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6732144768293313065709455 10098217152439969598564183)
              ·
                refine ⟨15147325728659954397846275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098217152439969598564183 15147325728659954397846275)
                ·
                  refine ⟨22720988592989931596769413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15147325728659954397846275 22720988592989931596769413)
                  ·
                    refine ⟨4260185361185612174394265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22720988592989931596769413 4260185361185612174394265)
                    ·
                      refine ⟨3195139020889209130795699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260185361185612174394265 3195139020889209130795699)
                      ·
                        rfl

theorem cell23_6222511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4, 2].length) (baseStart_6222511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222511 prefixEnd_6222511 := by exact prefixLift 6222511
  have htrace : WordTrace (prefixWord ++ tailWord_6222511) baseStart_6222511 baseEnd_6222511 := by
    simpa [prefixWord, tailWord_6222511, baseEnd_6222511] using wordTrace_append hprefix tailTrace_6222511
  have hstable : (prefixWord ++ tailWord_6222511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222511).length < 2 ^ (prefixWord ++ tailWord_6222511).sum := by decide
  have hdescent : baseEnd_6222511 < baseStart_6222511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222551 : List Nat := [1, 1, 3, 2, 1, 5, 3, 2, 5]
def baseStart_6222551 : Nat := 118140960795 + 6222551 * 2 ^ 59
def prefixEnd_6222551 : Nat := 4983230072969 + 3 ^ 40 * 6222551 * 2
def baseEnd_6222551 : Nat := 355017728901709886032835

theorem tailTrace_6222551 : CollatzResearch.WordTrace tailWord_6222551 prefixEnd_6222551 355017728901709886032835 := by
  unfold tailWord_6222551
  simp only [CollatzResearch.WordTrace]
  refine ⟨226955080079767928947883507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151303386719845285965255671 226955080079767928947883507)
  ·
    refine ⟨340432620119651893421825261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226955080079767928947883507 340432620119651893421825261)
    ·
      refine ⟨127662232544869460033184473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340432620119651893421825261 127662232544869460033184473)
      ·
        refine ⟨95746674408652095024888355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127662232544869460033184473 95746674408652095024888355)
        ·
          refine ⟨143620011612978142537332533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95746674408652095024888355 143620011612978142537332533)
          ·
            refine ⟨13464376088716700862874925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143620011612978142537332533 13464376088716700862874925)
            ·
              refine ⟨5049141033268762823578097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13464376088716700862874925 5049141033268762823578097)
              ·
                refine ⟨3786855774951572117683573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5049141033268762823578097 3786855774951572117683573)
                ·
                  refine ⟨355017728901709886032835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3786855774951572117683573 355017728901709886032835)
                  ·
                    rfl

theorem cell23_6222551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2, 5].length) (baseStart_6222551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222551 prefixEnd_6222551 := by exact prefixLift 6222551
  have htrace : WordTrace (prefixWord ++ tailWord_6222551) baseStart_6222551 baseEnd_6222551 := by
    simpa [prefixWord, tailWord_6222551, baseEnd_6222551] using wordTrace_append hprefix tailTrace_6222551
  have hstable : (prefixWord ++ tailWord_6222551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222551).length < 2 ^ (prefixWord ++ tailWord_6222551).sum := by decide
  have hdescent : baseEnd_6222551 < baseStart_6222551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222554 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2]
def baseStart_6222554 : Nat := 118140960795 + 6222554 * 2 ^ 59
def prefixEnd_6222554 : Nat := 4983230072969 + 3 ^ 40 * 6222554 * 2
def baseEnd_6222554 : Nat := 3195161100557352462558001

theorem tailTrace_6222554 : CollatzResearch.WordTrace tailWord_6222554 prefixEnd_6222554 3195161100557352462558001 := by
  unfold tailWord_6222554
  simp only [CollatzResearch.WordTrace]
  refine ⟨56738797374689265115060679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151303459665838040306828477 56738797374689265115060679)
  ·
    refine ⟨85108196062033897672591019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56738797374689265115060679 85108196062033897672591019)
    ·
      refine ⟨127662294093050846508886529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85108196062033897672591019 127662294093050846508886529)
      ·
        refine ⟨95746720569788134881664897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127662294093050846508886529 95746720569788134881664897)
        ·
          refine ⟨71810040427341101161248673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95746720569788134881664897 71810040427341101161248673)
          ·
            refine ⟨53857530320505825870936505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71810040427341101161248673 53857530320505825870936505)
            ·
              refine ⟨40393147740379369403202379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53857530320505825870936505 40393147740379369403202379)
              ·
                refine ⟨60589721610569054104803569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40393147740379369403202379 60589721610569054104803569)
                ·
                  refine ⟨45442291207926790578602677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60589721610569054104803569 45442291207926790578602677)
                  ·
                    refine ⟨4260214800743136616744001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45442291207926790578602677 4260214800743136616744001)
                    ·
                      refine ⟨3195161100557352462558001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4260214800743136616744001 3195161100557352462558001)
                      ·
                        rfl

theorem cell23_6222554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_6222554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222554 prefixEnd_6222554 := by exact prefixLift 6222554
  have htrace : WordTrace (prefixWord ++ tailWord_6222554) baseStart_6222554 baseEnd_6222554 := by
    simpa [prefixWord, tailWord_6222554, baseEnd_6222554] using wordTrace_append hprefix tailTrace_6222554
  have hstable : (prefixWord ++ tailWord_6222554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222554).length < 2 ^ (prefixWord ++ tailWord_6222554).sum := by decide
  have hdescent : baseEnd_6222554 < baseStart_6222554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222584 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_6222584 : Nat := 118140960795 + 6222584 * 2 ^ 59
def prefixEnd_6222584 : Nat := 4983230072969 + 3 ^ 40 * 6222584 * 2
def baseEnd_6222584 : Nat := 3195176504976987345182863

theorem tailTrace_6222584 : CollatzResearch.WordTrace tailWord_6222584 prefixEnd_6222584 3195176504976987345182863 := by
  unfold tailWord_6222584
  simp only [CollatzResearch.WordTrace]
  refine ⟨113478141844324187791917403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151304189125765583722556537 113478141844324187791917403)
  ·
    refine ⟨170217212766486281687876105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113478141844324187791917403 170217212766486281687876105)
    ·
      refine ⟨127662909574864711265907079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170217212766486281687876105 127662909574864711265907079)
      ·
        refine ⟨191494364362297066898860619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127662909574864711265907079 191494364362297066898860619)
        ·
          refine ⟨287241546543445600348290929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191494364362297066898860619 287241546543445600348290929)
          ·
            refine ⟨215431159907584200261218197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287241546543445600348290929 215431159907584200261218197)
            ·
              refine ⟨10098335620668009387244603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 215431159907584200261218197 10098335620668009387244603)
              ·
                refine ⟨15147503431002014080866905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10098335620668009387244603 15147503431002014080866905)
                ·
                  refine ⟨11360627573251510560650179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15147503431002014080866905 11360627573251510560650179)
                  ·
                    refine ⟨17040941359877265840975269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11360627573251510560650179 17040941359877265840975269)
                    ·
                      refine ⟨3195176504976987345182863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17040941359877265840975269 3195176504976987345182863)
                      ·
                        rfl

theorem cell23_6222584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_6222584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222584 prefixEnd_6222584 := by exact prefixLift 6222584
  have htrace : WordTrace (prefixWord ++ tailWord_6222584) baseStart_6222584 baseEnd_6222584 := by
    simpa [prefixWord, tailWord_6222584, baseEnd_6222584] using wordTrace_append hprefix tailTrace_6222584
  have hstable : (prefixWord ++ tailWord_6222584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222584).length < 2 ^ (prefixWord ++ tailWord_6222584).sum := by decide
  have hdescent : baseEnd_6222584 < baseStart_6222584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222587 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3]
def baseStart_6222587 : Nat := 118140960795 + 6222587 * 2 ^ 59
def prefixEnd_6222587 : Nat := 4983230072969 + 3 ^ 40 * 6222587 * 2
def baseEnd_6222587 : Nat := 3195178045418950833445349

theorem tailTrace_6222587 : CollatzResearch.WordTrace tailWord_6222587 prefixEnd_6222587 3195178045418950833445349 := by
  unfold tailWord_6222587
  simp only [CollatzResearch.WordTrace]
  refine ⟨226956393107637507096194015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151304262071758338064129343 226956393107637507096194015)
  ·
    refine ⟨340434589661456260644291023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226956393107637507096194015 340434589661456260644291023)
    ·
      refine ⟨510651884492184390966436535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340434589661456260644291023 510651884492184390966436535)
      ·
        refine ⟨765977826738276586449654803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510651884492184390966436535 765977826738276586449654803)
        ·
          refine ⟨1148966740107414879674482205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765977826738276586449654803 1148966740107414879674482205)
          ·
            refine ⟨430862527540280579877930827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1148966740107414879674482205 430862527540280579877930827)
            ·
              refine ⟨646293791310420869816896241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430862527540280579877930827 646293791310420869816896241)
              ·
                refine ⟨484720343482815652362672181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646293791310420869816896241 484720343482815652362672181)
                ·
                  refine ⟨45442532201513967409000517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 484720343482815652362672181 45442532201513967409000517)
                  ·
                    refine ⟨8520474787783868889187597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45442532201513967409000517 8520474787783868889187597)
                    ·
                      refine ⟨3195178045418950833445349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8520474787783868889187597 3195178045418950833445349)
                      ·
                        rfl

theorem cell23_6222587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 3].length) (baseStart_6222587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222587 prefixEnd_6222587 := by exact prefixLift 6222587
  have htrace : WordTrace (prefixWord ++ tailWord_6222587) baseStart_6222587 baseEnd_6222587 := by
    simpa [prefixWord, tailWord_6222587, baseEnd_6222587] using wordTrace_append hprefix tailTrace_6222587
  have hstable : (prefixWord ++ tailWord_6222587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222587).length < 2 ^ (prefixWord ++ tailWord_6222587).sum := by decide
  have hdescent : baseEnd_6222587 < baseStart_6222587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6222611 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 1, 4]
def baseStart_6222611 : Nat := 118140960795 + 6222611 * 2 ^ 59
def prefixEnd_6222611 : Nat := 4983230072969 + 3 ^ 40 * 6222611 * 2
def baseEnd_6222611 : Nat := 1065063456318219579848413

theorem tailTrace_6222611 : CollatzResearch.WordTrace tailWord_6222611 prefixEnd_6222611 1065063456318219579848413 := by
  unfold tailWord_6222611
  simp only [CollatzResearch.WordTrace]
  refine ⟨226957268459550559195067687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151304845639700372796711791 226957268459550559195067687)
  ·
    refine ⟨340435902689325838792601531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226957268459550559195067687 340435902689325838792601531)
    ·
      refine ⟨510653854033988758188902297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340435902689325838792601531 510653854033988758188902297)
      ·
        refine ⟨382990390525491568641676723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510653854033988758188902297 382990390525491568641676723)
        ·
          refine ⟨574485585788237352962515085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382990390525491568641676723 574485585788237352962515085)
          ·
            refine ⟨215432094670589007360943157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574485585788237352962515085 215432094670589007360943157)
            ·
              refine ⟨20196758875367719440088421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215432094670589007360943157 20196758875367719440088421)
              ·
                refine ⟨3786892289131447395016579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20196758875367719440088421 3786892289131447395016579)
                ·
                  refine ⟨5680338433697171092524869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3786892289131447395016579 5680338433697171092524869)
                  ·
                    refine ⟨1065063456318219579848413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680338433697171092524869 1065063456318219579848413)
                    ·
                      rfl

theorem cell23_6222611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 1, 4].length) (baseStart_6222611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6222611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6222611 prefixEnd_6222611 := by exact prefixLift 6222611
  have htrace : WordTrace (prefixWord ++ tailWord_6222611) baseStart_6222611 baseEnd_6222611 := by
    simpa [prefixWord, tailWord_6222611, baseEnd_6222611] using wordTrace_append hprefix tailTrace_6222611
  have hstable : (prefixWord ++ tailWord_6222611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6222611).length < 2 ^ (prefixWord ++ tailWord_6222611).sum := by decide
  have hdescent : baseEnd_6222611 < baseStart_6222611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6222611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
