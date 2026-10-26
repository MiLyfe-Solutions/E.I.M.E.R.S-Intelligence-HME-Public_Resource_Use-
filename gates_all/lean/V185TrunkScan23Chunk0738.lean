import V185TrunkScan23Chunk0737

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4363978 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_4363978 : Nat := 118140960795 + 4363978 * 2 ^ 59
def prefixEnd_4363978 : Nat := 4983230072969 + 3 ^ 40 * 4363978 * 2
def baseEnd_4363978 : Nat := 2240818279646632149705437

theorem tailTrace_4363978 : CollatzResearch.WordTrace tailWord_4363978 prefixEnd_4363978 2240818279646632149705437 := by
  unfold tailWord_4363978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791838446015122237625147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106111569189373659300333725 39791838446015122237625147)
  ·
    refine ⟨59687757669022683356437721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39791838446015122237625147 59687757669022683356437721)
    ·
      refine ⟨44765818251767012517328291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59687757669022683356437721 44765818251767012517328291)
      ·
        refine ⟨67148727377650518775992437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44765818251767012517328291 67148727377650518775992437)
        ·
          refine ⟨6295193191654736135249291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67148727377650518775992437 6295193191654736135249291)
          ·
            refine ⟨9442789787482104202873937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295193191654736135249291 9442789787482104202873937)
            ·
              refine ⟨7082092340611578152155453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442789787482104202873937 7082092340611578152155453)
              ·
                refine ⟨2655784627729341807058295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7082092340611578152155453 2655784627729341807058295)
                ·
                  refine ⟨3983676941594012710587443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655784627729341807058295 3983676941594012710587443)
                  ·
                    refine ⟨5975515412391019065881165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983676941594012710587443 5975515412391019065881165)
                    ·
                      refine ⟨2240818279646632149705437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975515412391019065881165 2240818279646632149705437)
                      ·
                        rfl

theorem cell23_4363978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_4363978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363978 prefixEnd_4363978 := by exact prefixLift 4363978
  have htrace : WordTrace (prefixWord ++ tailWord_4363978) baseStart_4363978 baseEnd_4363978 := by
    simpa [prefixWord, tailWord_4363978, baseEnd_4363978] using wordTrace_append hprefix tailTrace_4363978
  have hstable : (prefixWord ++ tailWord_4363978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363978).length < 2 ^ (prefixWord ++ tailWord_4363978).sum := by decide
  have hdescent : baseEnd_4363978 < baseStart_4363978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363981 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4363981 : Nat := 118140960795 + 4363981 * 2 ^ 59
def prefixEnd_4363981 : Nat := 4983230072969 + 3 ^ 40 * 4363981 * 2
def baseEnd_4363981 : Nat := 746939940029531879322641

theorem tailTrace_4363981 : CollatzResearch.WordTrace tailWord_4363981 prefixEnd_4363981 746939940029531879322641 := by
  unfold tailWord_4363981
  simp only [CollatzResearch.WordTrace]
  refine ⟨159167463203049620462859797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106111642135366413641906531 159167463203049620462859797)
  ·
    refine ⟨7460974837642950959196553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159167463203049620462859797 7460974837642950959196553)
    ·
      refine ⟨5595731128232213219397415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7460974837642950959196553 5595731128232213219397415)
      ·
        refine ⟨8393596692348319829096123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595731128232213219397415 8393596692348319829096123)
        ·
          refine ⟨12590395038522479743644185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8393596692348319829096123 12590395038522479743644185)
          ·
            refine ⟨9442796278891859807733139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12590395038522479743644185 9442796278891859807733139)
            ·
              refine ⟨14164194418337789711599709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442796278891859807733139 14164194418337789711599709)
              ·
                refine ⟨5311572906876671141849891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14164194418337789711599709 5311572906876671141849891)
                ·
                  refine ⟨7967359360315006712774837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311572906876671141849891 7967359360315006712774837)
                  ·
                    refine ⟨746939940029531879322641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7967359360315006712774837 746939940029531879322641)
                    ·
                      rfl

theorem cell23_4363981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4363981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363981 prefixEnd_4363981 := by exact prefixLift 4363981
  have htrace : WordTrace (prefixWord ++ tailWord_4363981) baseStart_4363981 baseEnd_4363981 := by
    simpa [prefixWord, tailWord_4363981, baseEnd_4363981] using wordTrace_append hprefix tailTrace_4363981
  have hstable : (prefixWord ++ tailWord_4363981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363981).length < 2 ^ (prefixWord ++ tailWord_4363981).sum := by decide
  have hdescent : baseEnd_4363981 < baseStart_4363981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363994 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_4363994 : Nat := 118140960795 + 4363994 * 2 ^ 59
def prefixEnd_4363994 : Nat := 4983230072969 + 3 ^ 40 * 4363994 * 2
def baseEnd_4363994 : Nat := 746942165112368029035121

theorem tailTrace_4363994 : CollatzResearch.WordTrace tailWord_4363994 prefixEnd_4363994 746942165112368029035121 := by
  unfold tailWord_4363994
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791984338000630920770759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106111958234668349122055357 39791984338000630920770759)
  ·
    refine ⟨59687976507000946381156139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39791984338000630920770759 59687976507000946381156139)
    ·
      refine ⟨89531964760501419571734209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59687976507000946381156139 89531964760501419571734209)
      ·
        refine ⟨67148973570376064678800657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89531964760501419571734209 67148973570376064678800657)
        ·
          refine ⟨50361730177782048509100493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67148973570376064678800657 50361730177782048509100493)
          ·
            refine ⟨18885648816668268190912685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50361730177782048509100493 18885648816668268190912685)
            ·
              refine ⟨7082118306250600571592257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18885648816668268190912685 7082118306250600571592257)
              ·
                refine ⟨5311588729687950428694193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7082118306250600571592257 5311588729687950428694193)
                ·
                  refine ⟨3983691547265962821520645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311588729687950428694193 3983691547265962821520645)
                  ·
                    refine ⟨746942165112368029035121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983691547265962821520645 746942165112368029035121)
                    ·
                      rfl

theorem cell23_4363994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_4363994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363994 prefixEnd_4363994 := by exact prefixLift 4363994
  have htrace : WordTrace (prefixWord ++ tailWord_4363994) baseStart_4363994 baseEnd_4363994 := by
    simpa [prefixWord, tailWord_4363994, baseEnd_4363994] using wordTrace_append hprefix tailTrace_4363994
  have hstable : (prefixWord ++ tailWord_4363994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363994).length < 2 ^ (prefixWord ++ tailWord_4363994).sum := by decide
  have hdescent : baseEnd_4363994 < baseStart_4363994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364034 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4364034 : Nat := 118140960795 + 4364034 * 2 ^ 59
def prefixEnd_4364034 : Nat := 4983230072969 + 3 ^ 40 * 4364034 * 2
def baseEnd_4364034 : Nat := 2240847034563283930605179

theorem tailTrace_4364034 : CollatzResearch.WordTrace tailWord_4364034 prefixEnd_4364034 2240847034563283930605179 := by
  unfold tailWord_4364034
  simp only [CollatzResearch.WordTrace]
  refine ⟨39792349067964402628634789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106112930847905073676359437 39792349067964402628634789)
  ·
    refine ⟨7461065450243325492869023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39792349067964402628634789 7461065450243325492869023)
    ·
      refine ⟨11191598175364988239303535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7461065450243325492869023 11191598175364988239303535)
      ·
        refine ⟨16787397263047482358955303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11191598175364988239303535 16787397263047482358955303)
        ·
          refine ⟨25181095894571223538432955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16787397263047482358955303 25181095894571223538432955)
          ·
            refine ⟨37771643841856835307649433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25181095894571223538432955 37771643841856835307649433)
            ·
              refine ⟨28328732881392626480737075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37771643841856835307649433 28328732881392626480737075)
              ·
                refine ⟨42493099322088939721105613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28328732881392626480737075 42493099322088939721105613)
                ·
                  refine ⟨15934912245783352395414605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42493099322088939721105613 15934912245783352395414605)
                  ·
                    refine ⟨5975592092168757148280477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15934912245783352395414605 5975592092168757148280477)
                    ·
                      refine ⟨2240847034563283930605179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975592092168757148280477 2240847034563283930605179)
                      ·
                        rfl

theorem cell23_4364034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4364034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364034 prefixEnd_4364034 := by exact prefixLift 4364034
  have htrace : WordTrace (prefixWord ++ tailWord_4364034) baseStart_4364034 baseEnd_4364034 := by
    simpa [prefixWord, tailWord_4364034, baseEnd_4364034] using wordTrace_append hprefix tailTrace_4364034
  have hstable : (prefixWord ++ tailWord_4364034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364034).length < 2 ^ (prefixWord ++ tailWord_4364034).sum := by decide
  have hdescent : baseEnd_4364034 < baseStart_4364034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364062 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4364062 : Nat := 118140960795 + 4364062 * 2 ^ 59
def prefixEnd_4364062 : Nat := 4983230072969 + 3 ^ 40 * 4364062 * 2
def baseEnd_4364062 : Nat := 746953804007203273685017

theorem tailTrace_4364062 : CollatzResearch.WordTrace tailWord_4364062 prefixEnd_4364062 746953804007203273685017 := by
  unfold tailWord_4364062
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896302189469521412069805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106113611677170780864372293 19896302189469521412069805)
  ·
    refine ⟨7461113321051070529526177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19896302189469521412069805 7461113321051070529526177)
    ·
      refine ⟨5595834990788302897144633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7461113321051070529526177 5595834990788302897144633)
      ·
        refine ⟨4196876243091227172858475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5595834990788302897144633 4196876243091227172858475)
        ·
          refine ⟨6295314364636840759287713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196876243091227172858475 6295314364636840759287713)
          ·
            refine ⟨4721485773477630569465785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6295314364636840759287713 4721485773477630569465785)
            ·
              refine ⟨3541114330108222927099339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721485773477630569465785 3541114330108222927099339)
              ·
                refine ⟨5311671495162334390649009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541114330108222927099339 5311671495162334390649009)
                ·
                  refine ⟨3983753621371750792986757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311671495162334390649009 3983753621371750792986757)
                  ·
                    refine ⟨746953804007203273685017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983753621371750792986757 746953804007203273685017)
                    ·
                      rfl

theorem cell23_4364062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4364062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364062 prefixEnd_4364062 := by exact prefixLift 4364062
  have htrace : WordTrace (prefixWord ++ tailWord_4364062) baseStart_4364062 baseEnd_4364062 := by
    simpa [prefixWord, tailWord_4364062, baseEnd_4364062] using wordTrace_append hprefix tailTrace_4364062
  have hstable : (prefixWord ++ tailWord_4364062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364062).length < 2 ^ (prefixWord ++ tailWord_4364062).sum := by decide
  have hdescent : baseEnd_4364062 < baseStart_4364062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364068 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_4364068 : Nat := 118140960795 + 4364068 * 2 ^ 59
def prefixEnd_4364068 : Nat := 4983230072969 + 3 ^ 40 * 4364068 * 2
def baseEnd_4364068 : Nat := 2240864492905536797580023

theorem tailTrace_4364068 : CollatzResearch.WordTrace tailWord_4364068 prefixEnd_4364068 2240864492905536797580023 := by
  unfold tailWord_4364068
  simp only [CollatzResearch.WordTrace]
  refine ⟨79585318176867217160638429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106113757569156289547517905 79585318176867217160638429)
  ·
    refine ⟨29844494316325206435239411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79585318176867217160638429 29844494316325206435239411)
    ·
      refine ⟨44766741474487809652859117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29844494316325206435239411 44766741474487809652859117)
      ·
        refine ⟨16787528052932928619822169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44766741474487809652859117 16787528052932928619822169)
        ·
          refine ⟨12590646039699696464866627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16787528052932928619822169 12590646039699696464866627)
          ·
            refine ⟨18885969059549544697299941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12590646039699696464866627 18885969059549544697299941)
            ·
              refine ⟨3541119198665539630743739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18885969059549544697299941 3541119198665539630743739)
              ·
                refine ⟨5311678797998309446115609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541119198665539630743739 5311678797998309446115609)
                ·
                  refine ⟨3983759098498732084586707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311678797998309446115609 3983759098498732084586707)
                  ·
                    refine ⟨5975638647748098126880061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983759098498732084586707 5975638647748098126880061)
                    ·
                      refine ⟨2240864492905536797580023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975638647748098126880061 2240864492905536797580023)
                      ·
                        rfl

theorem cell23_4364068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_4364068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364068 prefixEnd_4364068 := by exact prefixLift 4364068
  have htrace : WordTrace (prefixWord ++ tailWord_4364068) baseStart_4364068 baseEnd_4364068 := by
    simpa [prefixWord, tailWord_4364068, baseEnd_4364068] using wordTrace_append hprefix tailTrace_4364068
  have hstable : (prefixWord ++ tailWord_4364068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364068).length < 2 ^ (prefixWord ++ tailWord_4364068).sum := by decide
  have hdescent : baseEnd_4364068 < baseStart_4364068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364078 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4364078 : Nat := 118140960795 + 4364078 * 2 ^ 59
def prefixEnd_4364078 : Nat := 4983230072969 + 3 ^ 40 * 4364078 * 2
def baseEnd_4364078 : Nat := 2240869627712081758454977

theorem tailTrace_4364078 : CollatzResearch.WordTrace tailWord_4364078 prefixEnd_4364078 2240869627712081758454977 := by
  unfold tailWord_4364078
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896375135462275753642611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106114000722465470686093925 19896375135462275753642611)
  ·
    refine ⟨29844562703193413630463917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19896375135462275753642611 29844562703193413630463917)
    ·
      refine ⟨11191711013697530111423969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29844562703193413630463917 11191711013697530111423969)
      ·
        refine ⟨8393783260273147583567977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11191711013697530111423969 8393783260273147583567977)
        ·
          refine ⟨6295337445204860687675983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8393783260273147583567977 6295337445204860687675983)
          ·
            refine ⟨9443006167807291031513975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295337445204860687675983 9443006167807291031513975)
            ·
              refine ⟨14164509251710936547270963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9443006167807291031513975 14164509251710936547270963)
              ·
                refine ⟨21246763877566404820906445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14164509251710936547270963 21246763877566404820906445)
                ·
                  refine ⟨7967536454087401807839917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21246763877566404820906445 7967536454087401807839917)
                  ·
                    refine ⟨2987826170282775677939969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7967536454087401807839917 2987826170282775677939969)
                    ·
                      refine ⟨2240869627712081758454977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987826170282775677939969 2240869627712081758454977)
                      ·
                        rfl

theorem cell23_4364078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4364078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364078 prefixEnd_4364078 := by exact prefixLift 4364078
  have htrace : WordTrace (prefixWord ++ tailWord_4364078) baseStart_4364078 baseEnd_4364078 := by
    simpa [prefixWord, tailWord_4364078, baseEnd_4364078] using wordTrace_append hprefix tailTrace_4364078
  have hstable : (prefixWord ++ tailWord_4364078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364078).length < 2 ^ (prefixWord ++ tailWord_4364078).sum := by decide
  have hdescent : baseEnd_4364078 < baseStart_4364078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364094 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4364094 : Nat := 118140960795 + 4364094 * 2 ^ 59
def prefixEnd_4364094 : Nat := 4983230072969 + 3 ^ 40 * 4364094 * 2
def baseEnd_4364094 : Nat := 2240877843402553695854903

theorem tailTrace_4364094 : CollatzResearch.WordTrace tailWord_4364094 prefixEnd_4364094 2240877843402553695854903 := by
  unfold tailWord_4364094
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896448081455030095215417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106114389767760160507815557 19896448081455030095215417)
  ·
    refine ⟨14922336061091272571411563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19896448081455030095215417 14922336061091272571411563)
    ·
      refine ⟨22383504091636908857117345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14922336061091272571411563 22383504091636908857117345)
      ·
        refine ⟨16787628068727681642838009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22383504091636908857117345 16787628068727681642838009)
        ·
          refine ⟨12590721051545761232128507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16787628068727681642838009 12590721051545761232128507)
          ·
            refine ⟨18886081577318641848192761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12590721051545761232128507 18886081577318641848192761)
            ·
              refine ⟨14164561182988981386144571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18886081577318641848192761 14164561182988981386144571)
              ·
                refine ⟨21246841774483472079216857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14164561182988981386144571 21246841774483472079216857)
                ·
                  refine ⟨15935131330862604059412643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21246841774483472079216857 15935131330862604059412643)
                  ·
                    refine ⟨23902696996293906089118965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15935131330862604059412643 23902696996293906089118965)
                    ·
                      refine ⟨2240877843402553695854903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23902696996293906089118965 2240877843402553695854903)
                      ·
                        rfl

theorem cell23_4364094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4364094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364094 prefixEnd_4364094 := by exact prefixLift 4364094
  have htrace : WordTrace (prefixWord ++ tailWord_4364094) baseStart_4364094 baseEnd_4364094 := by
    simpa [prefixWord, tailWord_4364094, baseEnd_4364094] using wordTrace_append hprefix tailTrace_4364094
  have hstable : (prefixWord ++ tailWord_4364094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364094).length < 2 ^ (prefixWord ++ tailWord_4364094).sum := by decide
  have hdescent : baseEnd_4364094 < baseStart_4364094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364164 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_4364164 : Nat := 118140960795 + 4364164 * 2 ^ 59
def prefixEnd_4364164 : Nat := 4983230072969 + 3 ^ 40 * 4364164 * 2
def baseEnd_4364164 : Nat := 2240913787048368421979581

theorem tailTrace_4364164 : CollatzResearch.WordTrace tailWord_4364164 prefixEnd_4364164 2240913787048368421979581 := by
  unfold tailWord_4364164
  simp only [CollatzResearch.WordTrace]
  refine ⟨79587068880693321358385773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106116091840924428477847697 79587068880693321358385773)
  ·
    refine ⟨29845150830259995509394665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79587068880693321358385773 29845150830259995509394665)
    ·
      refine ⟨22383863122694996632045999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29845150830259995509394665 22383863122694996632045999)
      ·
        refine ⟨33575794684042494948068999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22383863122694996632045999 33575794684042494948068999)
        ·
          refine ⟨50363692026063742422103499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33575794684042494948068999 50363692026063742422103499)
          ·
            refine ⟨75545538039095613633155249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50363692026063742422103499 75545538039095613633155249)
            ·
              refine ⟨56659153529321710224866437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75545538039095613633155249 56659153529321710224866437)
              ·
                refine ⟨10623591286747820667162457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56659153529321710224866437 10623591286747820667162457)
                ·
                  refine ⟨7967693465060865500371843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10623591286747820667162457 7967693465060865500371843)
                  ·
                    refine ⟨11951540197591298250557765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7967693465060865500371843 11951540197591298250557765)
                    ·
                      refine ⟨2240913787048368421979581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11951540197591298250557765 2240913787048368421979581)
                      ·
                        rfl

theorem cell23_4364164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_4364164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364164 prefixEnd_4364164 := by exact prefixLift 4364164
  have htrace : WordTrace (prefixWord ++ tailWord_4364164) baseStart_4364164 baseEnd_4364164 := by
    simpa [prefixWord, tailWord_4364164, baseEnd_4364164] using wordTrace_append hprefix tailTrace_4364164
  have hstable : (prefixWord ++ tailWord_4364164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364164).length < 2 ^ (prefixWord ++ tailWord_4364164).sum := by decide
  have hdescent : baseEnd_4364164 < baseStart_4364164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364252 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4364252 : Nat := 118140960795 + 4364252 * 2 ^ 59
def prefixEnd_4364252 : Nat := 4983230072969 + 3 ^ 40 * 4364252 * 2
def baseEnd_4364252 : Nat := 2240958973345964077679177

theorem tailTrace_4364252 : CollatzResearch.WordTrace tailWord_4364252 prefixEnd_4364252 2240958973345964077679177 := by
  unfold tailWord_4364252
  simp only [CollatzResearch.WordTrace]
  refine ⟨79588673692533916872987505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106118231590045222497316673 79588673692533916872987505)
  ·
    refine ⟨59691505269400437654740629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79588673692533916872987505 59691505269400437654740629)
    ·
      refine ⟨2798039309503145515065967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59691505269400437654740629 2798039309503145515065967)
      ·
        refine ⟨4197058964254718272598951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798039309503145515065967 4197058964254718272598951)
        ·
          refine ⟨6295588446382077408898427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197058964254718272598951 6295588446382077408898427)
          ·
            refine ⟨9443382669573116113347641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295588446382077408898427 9443382669573116113347641)
            ·
              refine ⟨7082537002179837085010731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9443382669573116113347641 7082537002179837085010731)
              ·
                refine ⟨10623805503269755627516097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7082537002179837085010731 10623805503269755627516097)
                ·
                  refine ⟨7967854127452316720637073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10623805503269755627516097 7967854127452316720637073)
                  ·
                    refine ⟨5975890595589237540477805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7967854127452316720637073 5975890595589237540477805)
                    ·
                      refine ⟨2240958973345964077679177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975890595589237540477805 2240958973345964077679177)
                      ·
                        rfl

theorem cell23_4364252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4364252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364252 prefixEnd_4364252 := by exact prefixLift 4364252
  have htrace : WordTrace (prefixWord ++ tailWord_4364252) baseStart_4364252 baseEnd_4364252 := by
    simpa [prefixWord, tailWord_4364252, baseEnd_4364252] using wordTrace_append hprefix tailTrace_4364252
  have hstable : (prefixWord ++ tailWord_4364252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364252).length < 2 ^ (prefixWord ++ tailWord_4364252).sum := by decide
  have hdescent : baseEnd_4364252 < baseStart_4364252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364281 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_4364281 : Nat := 118140960795 + 4364281 * 2 ^ 59
def prefixEnd_4364281 : Nat := 4983230072969 + 3 ^ 40 * 4364281 * 2
def baseEnd_4364281 : Nat := 746991288094981488072181

theorem tailTrace_4364281 : CollatzResearch.WordTrace tailWord_4364281 prefixEnd_4364281 746991288094981488072181 := by
  unfold tailWord_4364281
  simp only [CollatzResearch.WordTrace]
  refine ⟨159178405101962771698780697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106118936734641847799187131 159178405101962771698780697)
  ·
    refine ⟨119383803826472078774085523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159178405101962771698780697 119383803826472078774085523)
    ·
      refine ⟨179075705739708118161128285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119383803826472078774085523 179075705739708118161128285)
      ·
        refine ⟨67153389652390544310423107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179075705739708118161128285 67153389652390544310423107)
        ·
          refine ⟨100730084478585816465634661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67153389652390544310423107 100730084478585816465634661)
          ·
            refine ⟨18886890839734840587306499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100730084478585816465634661 18886890839734840587306499)
            ·
              refine ⟨28330336259602260880959749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18886890839734840587306499 28330336259602260880959749)
              ·
                refine ⟨5311938048675423915179953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28330336259602260880959749 5311938048675423915179953)
                ·
                  refine ⟨3983953536506567936384965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311938048675423915179953 3983953536506567936384965)
                  ·
                    refine ⟨746991288094981488072181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983953536506567936384965 746991288094981488072181)
                    ·
                      rfl

theorem cell23_4364281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_4364281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364281 prefixEnd_4364281 := by exact prefixLift 4364281
  have htrace : WordTrace (prefixWord ++ tailWord_4364281) baseStart_4364281 baseEnd_4364281 := by
    simpa [prefixWord, tailWord_4364281, baseEnd_4364281] using wordTrace_append hprefix tailTrace_4364281
  have hstable : (prefixWord ++ tailWord_4364281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364281).length < 2 ^ (prefixWord ++ tailWord_4364281).sum := by decide
  have hdescent : baseEnd_4364281 < baseStart_4364281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364284 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_4364284 : Nat := 118140960795 + 4364284 * 2 ^ 59
def prefixEnd_4364284 : Nat := 4983230072969 + 3 ^ 40 * 4364284 * 2
def baseEnd_4364284 : Nat := 2240975404726907952479029

theorem tailTrace_4364284 : CollatzResearch.WordTrace tailWord_4364284 prefixEnd_4364284 2240975404726907952479029 := by
  unfold tailWord_4364284
  simp only [CollatzResearch.WordTrace]
  refine ⟨79589257260475951605569953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106119009680634602140759937 79589257260475951605569953)
  ·
    refine ⟨59691942945356963704177465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79589257260475951605569953 59691942945356963704177465)
    ·
      refine ⟨44768957209017722778133099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59691942945356963704177465 44768957209017722778133099)
      ·
        refine ⟨67153435813526584167199649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44768957209017722778133099 67153435813526584167199649)
        ·
          refine ⟨50365076860144938125399737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67153435813526584167199649 50365076860144938125399737)
          ·
            refine ⟨37773807645108703594049803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50365076860144938125399737 37773807645108703594049803)
            ·
              refine ⟨56660711467663055391074705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37773807645108703594049803 56660711467663055391074705)
              ·
                refine ⟨42495533600747291543306029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56660711467663055391074705 42495533600747291543306029)
                ·
                  refine ⟨15935825100280234328739761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42495533600747291543306029 15935825100280234328739761)
                  ·
                    refine ⟨11951868825210175746554821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15935825100280234328739761 11951868825210175746554821)
                    ·
                      refine ⟨2240975404726907952479029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11951868825210175746554821 2240975404726907952479029)
                      ·
                        rfl

theorem cell23_4364284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_4364284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364284 prefixEnd_4364284 := by exact prefixLift 4364284
  have htrace : WordTrace (prefixWord ++ tailWord_4364284) baseStart_4364284 baseEnd_4364284 := by
    simpa [prefixWord, tailWord_4364284, baseEnd_4364284] using wordTrace_append hprefix tailTrace_4364284
  have hstable : (prefixWord ++ tailWord_4364284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364284).length < 2 ^ (prefixWord ++ tailWord_4364284).sum := by decide
  have hdescent : baseEnd_4364284 < baseStart_4364284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_4364304 : Nat := 118140960795 + 4364304 * 2 ^ 59
def prefixEnd_4364304 : Nat := 4983230072969 + 3 ^ 40 * 4364304 * 2
def baseEnd_4364304 : Nat := 2240985674339997874228937

theorem tailTrace_4364304 : CollatzResearch.WordTrace tailWord_4364304 prefixEnd_4364304 2240985674339997874228937 := by
  unfold tailWord_4364304
  simp only [CollatzResearch.WordTrace]
  refine ⟨79589621990439723313433983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106119495987252964417911977 79589621990439723313433983)
  ·
    refine ⟨119384432985659584970150975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79589621990439723313433983 119384432985659584970150975)
    ·
      refine ⟨179076649478489377455226463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119384432985659584970150975 179076649478489377455226463)
      ·
        refine ⟨268614974217734066182839695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179076649478489377455226463 268614974217734066182839695)
        ·
          refine ⟨402922461326601099274259543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268614974217734066182839695 402922461326601099274259543)
          ·
            refine ⟨604383691989901648911389315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402922461326601099274259543 604383691989901648911389315)
            ·
              refine ⟨906575537984852473367083973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604383691989901648911389315 906575537984852473367083973)
              ·
                refine ⟨169982913372159838756328245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 906575537984852473367083973 169982913372159838756328245)
                ·
                  refine ⟨15935898128639984883405773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169982913372159838756328245 15935898128639984883405773)
                  ·
                    refine ⟨5975961798239994331277165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15935898128639984883405773 5975961798239994331277165)
                    ·
                      refine ⟨2240985674339997874228937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975961798239994331277165 2240985674339997874228937)
                      ·
                        rfl

theorem cell23_4364304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_4364304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364304 prefixEnd_4364304 := by exact prefixLift 4364304
  have htrace : WordTrace (prefixWord ++ tailWord_4364304) baseStart_4364304 baseEnd_4364304 := by
    simpa [prefixWord, tailWord_4364304, baseEnd_4364304] using wordTrace_append hprefix tailTrace_4364304
  have hstable : (prefixWord ++ tailWord_4364304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364304).length < 2 ^ (prefixWord ++ tailWord_4364304).sum := by decide
  have hdescent : baseEnd_4364304 < baseStart_4364304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364322 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_4364322 : Nat := 118140960795 + 4364322 * 2 ^ 59
def prefixEnd_4364322 : Nat := 4983230072969 + 3 ^ 40 * 4364322 * 2
def baseEnd_4364322 : Nat := 2240994916991778803803855

theorem tailTrace_4364322 : CollatzResearch.WordTrace tailWord_4364322 prefixEnd_4364322 2240994916991778803803855 := by
  unfold tailWord_4364322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39794975123703558925255805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106119933663209490467348813 39794975123703558925255805)
  ·
    refine ⟨14923115671388834596970927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39794975123703558925255805 14923115671388834596970927)
    ·
      refine ⟨22384673507083251895456391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923115671388834596970927 22384673507083251895456391)
      ·
        refine ⟨33577010260624877843184587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22384673507083251895456391 33577010260624877843184587)
        ·
          refine ⟨50365515390937316764776881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33577010260624877843184587 50365515390937316764776881)
          ·
            refine ⟨37774136543202987573582661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50365515390937316764776881 37774136543202987573582661)
            ·
              refine ⟨7082650601850560170046749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37774136543202987573582661 7082650601850560170046749)
              ·
                refine ⟨2655993975693960063767531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7082650601850560170046749 2655993975693960063767531)
                ·
                  refine ⟨3983990963540940095651297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655993975693960063767531 3983990963540940095651297)
                  ·
                    refine ⟨2987993222655705071738473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983990963540940095651297 2987993222655705071738473)
                    ·
                      refine ⟨2240994916991778803803855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987993222655705071738473 2240994916991778803803855)
                      ·
                        rfl

theorem cell23_4364322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_4364322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364322 prefixEnd_4364322 := by exact prefixLift 4364322
  have htrace : WordTrace (prefixWord ++ tailWord_4364322) baseStart_4364322 baseEnd_4364322 := by
    simpa [prefixWord, tailWord_4364322, baseEnd_4364322] using wordTrace_append hprefix tailTrace_4364322
  have hstable : (prefixWord ++ tailWord_4364322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364322).length < 2 ^ (prefixWord ++ tailWord_4364322).sum := by decide
  have hdescent : baseEnd_4364322 < baseStart_4364322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364325 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_4364325 : Nat := 118140960795 + 4364325 * 2 ^ 59
def prefixEnd_4364325 : Nat := 4983230072969 + 3 ^ 40 * 4364325 * 2
def baseEnd_4364325 : Nat := 2240996457433742292066341

theorem tailTrace_4364325 : CollatzResearch.WordTrace tailWord_4364325 prefixEnd_4364325 2240996457433742292066341 := by
  unfold tailWord_4364325
  simp only [CollatzResearch.WordTrace]
  refine ⟨159180009913803367213382429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106120006609202244808921619 159180009913803367213382429)
  ·
    refine ⟨59692503717676262705018411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159180009913803367213382429 59692503717676262705018411)
    ·
      refine ⟨89538755576514394057527617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59692503717676262705018411 89538755576514394057527617)
      ·
        refine ⟨67154066682385795543145713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89538755576514394057527617 67154066682385795543145713)
        ·
          refine ⟨50365550011789346657359285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67154066682385795543145713 50365550011789346657359285)
          ·
            refine ⟨4721770313605251249127433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50365550011789346657359285 4721770313605251249127433)
            ·
              refine ⟨3541327735203938436845575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721770313605251249127433 3541327735203938436845575)
              ·
                refine ⟨5311991602805907655268363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541327735203938436845575 5311991602805907655268363)
                ·
                  refine ⟨7967987404208861482902545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311991602805907655268363 7967987404208861482902545)
                  ·
                    refine ⟨5975990553156646112176909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7967987404208861482902545 5975990553156646112176909)
                    ·
                      refine ⟨2240996457433742292066341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975990553156646112176909 2240996457433742292066341)
                      ·
                        rfl

theorem cell23_4364325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_4364325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364325 prefixEnd_4364325 := by exact prefixLift 4364325
  have htrace : WordTrace (prefixWord ++ tailWord_4364325) baseStart_4364325 baseEnd_4364325 := by
    simpa [prefixWord, tailWord_4364325, baseEnd_4364325] using wordTrace_append hprefix tailTrace_4364325
  have hstable : (prefixWord ++ tailWord_4364325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364325).length < 2 ^ (prefixWord ++ tailWord_4364325).sum := by decide
  have hdescent : baseEnd_4364325 < baseStart_4364325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364331 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 5, 3, 2]
def baseStart_4364331 : Nat := 118140960795 + 4364331 * 2 ^ 59
def prefixEnd_4364331 : Nat := 4983230072969 + 3 ^ 40 * 4364331 * 2
def baseEnd_4364331 : Nat := 2240999538317669268591313

theorem tailTrace_4364331 : CollatzResearch.WordTrace tailWord_4364331 prefixEnd_4364331 2240999538317669268591313 := by
  unfold tailWord_4364331
  simp only [CollatzResearch.WordTrace]
  refine ⟨159180228751781630238100847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106120152501187753492067231 159180228751781630238100847)
  ·
    refine ⟨238770343127672445357151271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159180228751781630238100847 238770343127672445357151271)
    ·
      refine ⟨358155514691508668035726907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238770343127672445357151271 358155514691508668035726907)
      ·
        refine ⟨537233272037263002053590361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358155514691508668035726907 537233272037263002053590361)
        ·
          refine ⟨402924954027947251540192771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537233272037263002053590361 402924954027947251540192771)
          ·
            refine ⟨604387431041920877310289157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402924954027947251540192771 604387431041920877310289157)
            ·
              refine ⟨113322643320360164495679217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 604387431041920877310289157 113322643320360164495679217)
              ·
                refine ⟨84991982490270123371759413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113322643320360164495679217 84991982490270123371759413)
                ·
                  refine ⟨7967998358462824066102445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84991982490270123371759413 7967998358462824066102445)
                  ·
                    refine ⟨2987999384423559024788417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7967998358462824066102445 2987999384423559024788417)
                    ·
                      refine ⟨2240999538317669268591313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987999384423559024788417 2240999538317669268591313)
                      ·
                        rfl

theorem cell23_4364331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3, 2].length) (baseStart_4364331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364331 prefixEnd_4364331 := by exact prefixLift 4364331
  have htrace : WordTrace (prefixWord ++ tailWord_4364331) baseStart_4364331 baseEnd_4364331 := by
    simpa [prefixWord, tailWord_4364331, baseEnd_4364331] using wordTrace_append hprefix tailTrace_4364331
  have hstable : (prefixWord ++ tailWord_4364331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364331).length < 2 ^ (prefixWord ++ tailWord_4364331).sum := by decide
  have hdescent : baseEnd_4364331 < baseStart_4364331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364338 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_4364338 : Nat := 118140960795 + 4364338 * 2 ^ 59
def prefixEnd_4364338 : Nat := 4983230072969 + 3 ^ 40 * 4364338 * 2
def baseEnd_4364338 : Nat := 2241003132682250741203781

theorem tailTrace_4364338 : CollatzResearch.WordTrace tailWord_4364338 prefixEnd_4364338 2241003132682250741203781 := by
  unfold tailWord_4364338
  simp only [CollatzResearch.WordTrace]
  refine ⟨39795121015689067608401417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106120322708504180289070445 39795121015689067608401417)
  ·
    refine ⟨29846340761766800706301063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39795121015689067608401417 29846340761766800706301063)
    ·
      refine ⟨44769511142650201059451595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29846340761766800706301063 44769511142650201059451595)
      ·
        refine ⟨67154266713975301589177393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44769511142650201059451595 67154266713975301589177393)
        ·
          refine ⟨50365700035481476191883045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67154266713975301589177393 50365700035481476191883045)
          ·
            refine ⟨9443568756652776785978071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50365700035481476191883045 9443568756652776785978071)
            ·
              refine ⟨14165353134979165178967107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9443568756652776785978071 14165353134979165178967107)
              ·
                refine ⟨21248029702468747768450661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14165353134979165178967107 21248029702468747768450661)
                ·
                  refine ⟨3984005569212890206584499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21248029702468747768450661 3984005569212890206584499)
                  ·
                    refine ⟨5976008353819335309876749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3984005569212890206584499 5976008353819335309876749)
                    ·
                      refine ⟨2241003132682250741203781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5976008353819335309876749 2241003132682250741203781)
                      ·
                        rfl

theorem cell23_4364338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_4364338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364338 prefixEnd_4364338 := by exact prefixLift 4364338
  have htrace : WordTrace (prefixWord ++ tailWord_4364338) baseStart_4364338 baseEnd_4364338 := by
    simpa [prefixWord, tailWord_4364338, baseEnd_4364338] using wordTrace_append hprefix tailTrace_4364338
  have hstable : (prefixWord ++ tailWord_4364338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364338).length < 2 ^ (prefixWord ++ tailWord_4364338).sum := by decide
  have hdescent : baseEnd_4364338 < baseStart_4364338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364378 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_4364378 : Nat := 118140960795 + 4364378 * 2 ^ 59
def prefixEnd_4364378 : Nat := 4983230072969 + 3 ^ 40 * 4364378 * 2
def baseEnd_4364378 : Nat := 2241023671908430584703597

theorem tailTrace_4364378 : CollatzResearch.WordTrace tailWord_4364378 prefixEnd_4364378 2241023671908430584703597 := by
  unfold tailWord_4364378
  simp only [CollatzResearch.WordTrace]
  refine ⟨39795485745652839316265447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106121295321740904843374525 39795485745652839316265447)
  ·
    refine ⟨59693228618479258974398171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39795485745652839316265447 59693228618479258974398171)
    ·
      refine ⟨89539842927718888461597257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59693228618479258974398171 89539842927718888461597257)
      ·
        refine ⟨67154882195789166346197943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89539842927718888461597257 67154882195789166346197943)
        ·
          refine ⟨100732323293683749519296915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67154882195789166346197943 100732323293683749519296915)
          ·
            refine ⟨151098484940525624278945373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100732323293683749519296915 151098484940525624278945373)
            ·
              refine ⟨56661931852697109104604515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151098484940525624278945373 56661931852697109104604515)
              ·
                refine ⟨84992897779045663656906773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56661931852697109104604515 84992897779045663656906773)
                ·
                  refine ⟨3984042083392765483917505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84992897779045663656906773 3984042083392765483917505)
                  ·
                    refine ⟨2988031562544574112938129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984042083392765483917505 2988031562544574112938129)
                    ·
                      refine ⟨2241023671908430584703597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988031562544574112938129 2241023671908430584703597)
                      ·
                        rfl

theorem cell23_4364378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_4364378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364378 prefixEnd_4364378 := by exact prefixLift 4364378
  have htrace : WordTrace (prefixWord ++ tailWord_4364378) baseStart_4364378 baseEnd_4364378 := by
    simpa [prefixWord, tailWord_4364378, baseEnd_4364378] using wordTrace_append hprefix tailTrace_4364378
  have hstable : (prefixWord ++ tailWord_4364378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364378).length < 2 ^ (prefixWord ++ tailWord_4364378).sum := by decide
  have hdescent : baseEnd_4364378 < baseStart_4364378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364412 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_4364412 : Nat := 118140960795 + 4364412 * 2 ^ 59
def prefixEnd_4364412 : Nat := 4983230072969 + 3 ^ 40 * 4364412 * 2
def baseEnd_4364412 : Nat := 2241041130250683451678441

theorem tailTrace_4364412 : CollatzResearch.WordTrace tailWord_4364412 prefixEnd_4364412 2241041130250683451678441 := by
  unfold tailWord_4364412
  simp only [CollatzResearch.WordTrace]
  refine ⟨79591591532244090535899745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106122122042992120714532993 79591591532244090535899745)
  ·
    refine ⟨59693693649183067901924809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79591591532244090535899745 59693693649183067901924809)
    ·
      refine ⟨44770270236887300926443607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59693693649183067901924809 44770270236887300926443607)
      ·
        refine ⟨67155405355330951389665411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44770270236887300926443607 67155405355330951389665411)
        ·
          refine ⟨100733108032996427084498117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67155405355330951389665411 100733108032996427084498117)
          ·
            refine ⟨18887457756186830078343397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100733108032996427084498117 18887457756186830078343397)
            ·
              refine ⟨3541398329285030639689387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18887457756186830078343397 3541398329285030639689387)
              ·
                refine ⟨5312097493927545959534081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541398329285030639689387 5312097493927545959534081)
                ·
                  refine ⟨3984073120445659469650561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5312097493927545959534081 3984073120445659469650561)
                  ·
                    refine ⟨2988054840334244602237921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984073120445659469650561 2988054840334244602237921)
                    ·
                      refine ⟨2241041130250683451678441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988054840334244602237921 2241041130250683451678441)
                      ·
                        rfl

theorem cell23_4364412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_4364412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364412 prefixEnd_4364412 := by exact prefixLift 4364412
  have htrace : WordTrace (prefixWord ++ tailWord_4364412) baseStart_4364412 baseEnd_4364412 := by
    simpa [prefixWord, tailWord_4364412, baseEnd_4364412] using wordTrace_append hprefix tailTrace_4364412
  have hstable : (prefixWord ++ tailWord_4364412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364412).length < 2 ^ (prefixWord ++ tailWord_4364412).sum := by decide
  have hdescent : baseEnd_4364412 < baseStart_4364412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364452 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 5]
def baseStart_4364452 : Nat := 118140960795 + 4364452 * 2 ^ 59
def prefixEnd_4364452 : Nat := 4983230072969 + 3 ^ 40 * 4364452 * 2
def baseEnd_4364452 : Nat := 249006852164095921686473

theorem tailTrace_4364452 : CollatzResearch.WordTrace tailWord_4364452 prefixEnd_4364452 249006852164095921686473 := by
  unfold tailWord_4364452
  simp only [CollatzResearch.WordTrace]
  refine ⟨79592320992171633951627805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106123094656228845268837073 79592320992171633951627805)
  ·
    refine ⟨29847120372064362731860427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79592320992171633951627805 29847120372064362731860427)
    ·
      refine ⟨44770680558096544097790641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29847120372064362731860427 44770680558096544097790641)
      ·
        refine ⟨33578010418572408073342981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44770680558096544097790641 33578010418572408073342981)
        ·
          refine ⟨6295876953482326513751809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33578010418572408073342981 6295876953482326513751809)
          ·
            refine ⟨4721907715111744885313857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6295876953482326513751809 4721907715111744885313857)
            ·
              refine ⟨3541430786333808663985393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721907715111744885313857 3541430786333808663985393)
              ·
                refine ⟨2656073089750356497989045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541430786333808663985393 2656073089750356497989045)
                ·
                  refine ⟨249006852164095921686473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656073089750356497989045 249006852164095921686473)
                  ·
                    rfl

theorem cell23_4364452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_4364452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364452 prefixEnd_4364452 := by exact prefixLift 4364452
  have htrace : WordTrace (prefixWord ++ tailWord_4364452) baseStart_4364452 baseEnd_4364452 := by
    simpa [prefixWord, tailWord_4364452, baseEnd_4364452] using wordTrace_append hprefix tailTrace_4364452
  have hstable : (prefixWord ++ tailWord_4364452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364452).length < 2 ^ (prefixWord ++ tailWord_4364452).sum := by decide
  have hdescent : baseEnd_4364452 < baseStart_4364452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364462 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4364462 : Nat := 118140960795 + 4364462 * 2 ^ 59
def prefixEnd_4364462 : Nat := 4983230072969 + 3 ^ 40 * 4364462 * 2
def baseEnd_4364462 : Nat := 2241066804283408256053211

theorem tailTrace_4364462 : CollatzResearch.WordTrace tailWord_4364462 prefixEnd_4364462 2241066804283408256053211 := by
  unfold tailWord_4364462
  simp only [CollatzResearch.WordTrace]
  refine ⟨19898125839288379951389955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106123337809538026407413093 19898125839288379951389955)
  ·
    refine ⟨29847188758932569927084933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19898125839288379951389955 29847188758932569927084933)
    ·
      refine ⟨5596347892299856861328425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29847188758932569927084933 5596347892299856861328425)
      ·
        refine ⟨4197260919224892645996319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5596347892299856861328425 4197260919224892645996319)
        ·
          refine ⟨6295891378837338968994479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197260919224892645996319 6295891378837338968994479)
          ·
            refine ⟨9443837068256008453491719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295891378837338968994479 9443837068256008453491719)
            ·
              refine ⟨14165755602384012680237579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9443837068256008453491719 14165755602384012680237579)
              ·
                refine ⟨21248633403576019020356369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14165755602384012680237579 21248633403576019020356369)
                ·
                  refine ⟨15936475052682014265267277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21248633403576019020356369 15936475052682014265267277)
                  ·
                    refine ⟨5976178144755755349475229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15936475052682014265267277 5976178144755755349475229)
                    ·
                      refine ⟨2241066804283408256053211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5976178144755755349475229 2241066804283408256053211)
                      ·
                        rfl

theorem cell23_4364462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4364462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364462 prefixEnd_4364462 := by exact prefixLift 4364462
  have htrace : WordTrace (prefixWord ++ tailWord_4364462) baseStart_4364462 baseEnd_4364462 := by
    simpa [prefixWord, tailWord_4364462, baseEnd_4364462] using wordTrace_append hprefix tailTrace_4364462
  have hstable : (prefixWord ++ tailWord_4364462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364462).length < 2 ^ (prefixWord ++ tailWord_4364462).sum := by decide
  have hdescent : baseEnd_4364462 < baseStart_4364462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364482 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4364482 : Nat := 118140960795 + 4364482 * 2 ^ 59
def prefixEnd_4364482 : Nat := 4983230072969 + 3 ^ 40 * 4364482 * 2
def baseEnd_4364482 : Nat := 747025691298832725934373

theorem tailTrace_4364482 : CollatzResearch.WordTrace tailWord_4364482 prefixEnd_4364482 747025691298832725934373 := by
  unfold tailWord_4364482
  simp only [CollatzResearch.WordTrace]
  refine ⟨39796434043558645756711925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106123824116156388684565133 39796434043558645756711925)
  ·
    refine ⟨3730915691583623039691743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39796434043558645756711925 3730915691583623039691743)
    ·
      refine ⟨5596373537375434559537615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730915691583623039691743 5596373537375434559537615)
      ·
        refine ⟨8394560306063151839306423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5596373537375434559537615 8394560306063151839306423)
        ·
          refine ⟨12591840459094727758959635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8394560306063151839306423 12591840459094727758959635)
          ·
            refine ⟨18887760688642091638439453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12591840459094727758959635 18887760688642091638439453)
            ·
              refine ⟨7082910258240784364414795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18887760688642091638439453 7082910258240784364414795)
              ·
                refine ⟨10624365387361176546622193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7082910258240784364414795 10624365387361176546622193)
                ·
                  refine ⟨7968274040520882409966645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10624365387361176546622193 7968274040520882409966645)
                  ·
                    refine ⟨747025691298832725934373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7968274040520882409966645 747025691298832725934373)
                    ·
                      rfl

theorem cell23_4364482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4364482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364482 prefixEnd_4364482 := by exact prefixLift 4364482
  have htrace : WordTrace (prefixWord ++ tailWord_4364482) baseStart_4364482 baseEnd_4364482 := by
    simpa [prefixWord, tailWord_4364482, baseEnd_4364482] using wordTrace_append hprefix tailTrace_4364482
  have hstable : (prefixWord ++ tailWord_4364482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364482).length < 2 ^ (prefixWord ++ tailWord_4364482).sum := by decide
  have hdescent : baseEnd_4364482 < baseStart_4364482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364495 : List Nat := [1, 1, 2, 1, 1, 3, 6, 3, 1, 4]
def baseStart_4364495 : Nat := 118140960795 + 4364495 * 2 ^ 59
def prefixEnd_4364495 : Nat := 4983230072969 + 3 ^ 40 * 4364495 * 2
def baseEnd_4364495 : Nat := 747027916381668875646853

theorem tailTrace_4364495 : CollatzResearch.WordTrace tailWord_4364495 prefixEnd_4364495 747027916381668875646853 := by
  unfold tailWord_4364495
  simp only [CollatzResearch.WordTrace]
  refine ⟨159186210323187486247070939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106124140215458324164713959 159186210323187486247070939)
  ·
    refine ⟨238779315484781229370606409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159186210323187486247070939 238779315484781229370606409)
    ·
      refine ⟨179084486613585922027954807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238779315484781229370606409 179084486613585922027954807)
      ·
        refine ⟨268626729920378883041932211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179084486613585922027954807 268626729920378883041932211)
        ·
          refine ⟨402940094880568324562898317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268626729920378883041932211 402940094880568324562898317)
          ·
            refine ⟨151102535580213121711086869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402940094880568324562898317 151102535580213121711086869)
            ·
              refine ⟨7082931355322490080207197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 151102535580213121711086869 7082931355322490080207197)
              ·
                refine ⟨2656099258245933780077699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7082931355322490080207197 2656099258245933780077699)
                ·
                  refine ⟨3984148887368900670116549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656099258245933780077699 3984148887368900670116549)
                  ·
                    refine ⟨747027916381668875646853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984148887368900670116549 747027916381668875646853)
                    ·
                      rfl

theorem cell23_4364495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 1, 4].length) (baseStart_4364495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364495 prefixEnd_4364495 := by exact prefixLift 4364495
  have htrace : WordTrace (prefixWord ++ tailWord_4364495) baseStart_4364495 baseEnd_4364495 := by
    simpa [prefixWord, tailWord_4364495, baseEnd_4364495] using wordTrace_append hprefix tailTrace_4364495
  have hstable : (prefixWord ++ tailWord_4364495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364495).length < 2 ^ (prefixWord ++ tailWord_4364495).sum := by decide
  have hdescent : baseEnd_4364495 < baseStart_4364495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364502 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4364502 : Nat := 118140960795 + 4364502 * 2 ^ 59
def prefixEnd_4364502 : Nat := 4983230072969 + 3 ^ 40 * 4364502 * 2
def baseEnd_4364502 : Nat := 2241087343509588099553027

theorem tailTrace_4364502 : CollatzResearch.WordTrace tailWord_4364502 prefixEnd_4364502 2241087343509588099553027 := by
  unfold tailWord_4364502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949154102135132902660985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106124310422774750961717173 9949154102135132902660985)
  ·
    refine ⟨7461865576601349676995739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9949154102135132902660985 7461865576601349676995739)
    ·
      refine ⟨11192798364902024515493609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7461865576601349676995739 11192798364902024515493609)
      ·
        refine ⟨8394598773676518386620207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11192798364902024515493609 8394598773676518386620207)
        ·
          refine ⟨12591898160514777579930311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8394598773676518386620207 12591898160514777579930311)
          ·
            refine ⟨18887847240772166369895467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12591898160514777579930311 18887847240772166369895467)
            ·
              refine ⟨28331770861158249554843201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18887847240772166369895467 28331770861158249554843201)
              ·
                refine ⟨21248828145868687166132401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28331770861158249554843201 21248828145868687166132401)
                ·
                  refine ⟨15936621109401515374599301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21248828145868687166132401 15936621109401515374599301)
                  ·
                    refine ⟨2988116458012784132737369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15936621109401515374599301 2988116458012784132737369)
                    ·
                      refine ⟨2241087343509588099553027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988116458012784132737369 2241087343509588099553027)
                      ·
                        rfl

theorem cell23_4364502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4364502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364502 prefixEnd_4364502 := by exact prefixLift 4364502
  have htrace : WordTrace (prefixWord ++ tailWord_4364502) baseStart_4364502 baseEnd_4364502 := by
    simpa [prefixWord, tailWord_4364502, baseEnd_4364502] using wordTrace_append hprefix tailTrace_4364502
  have hstable : (prefixWord ++ tailWord_4364502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364502).length < 2 ^ (prefixWord ++ tailWord_4364502).sum := by decide
  have hdescent : baseEnd_4364502 < baseStart_4364502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364538 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_4364538 : Nat := 118140960795 + 4364538 * 2 ^ 59
def prefixEnd_4364538 : Nat := 4983230072969 + 3 ^ 40 * 4364538 * 2
def baseEnd_4364538 : Nat := 747035276271049986234287

theorem tailTrace_4364538 : CollatzResearch.WordTrace tailWord_4364538 prefixEnd_4364538 747035276271049986234287 := by
  unfold tailWord_4364538
  simp only [CollatzResearch.WordTrace]
  refine ⟨39796944665507926147721567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106125185774687803060590845 39796944665507926147721567)
  ·
    refine ⟨59695416998261889221582351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39796944665507926147721567 59695416998261889221582351)
    ·
      refine ⟨89543125497392833832373527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59695416998261889221582351 89543125497392833832373527)
      ·
        refine ⟨134314688246089250748560291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89543125497392833832373527 134314688246089250748560291)
        ·
          refine ⟨201472032369133876122840437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134314688246089250748560291 201472032369133876122840437)
          ·
            refine ⟨18888003034606300886516291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201472032369133876122840437 18888003034606300886516291)
            ·
              refine ⟨28332004551909451329774437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18888003034606300886516291 28332004551909451329774437)
              ·
                refine ⟨5312250853483022124332707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28332004551909451329774437 5312250853483022124332707)
                ·
                  refine ⟨7968376280224533186499061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5312250853483022124332707 7968376280224533186499061)
                  ·
                    refine ⟨747035276271049986234287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7968376280224533186499061 747035276271049986234287)
                    ·
                      rfl

theorem cell23_4364538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_4364538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364538 prefixEnd_4364538 := by exact prefixLift 4364538
  have htrace : WordTrace (prefixWord ++ tailWord_4364538) baseStart_4364538 baseEnd_4364538 := by
    simpa [prefixWord, tailWord_4364538, baseEnd_4364538] using wordTrace_append hprefix tailTrace_4364538
  have hstable : (prefixWord ++ tailWord_4364538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364538).length < 2 ^ (prefixWord ++ tailWord_4364538).sum := by decide
  have hdescent : baseEnd_4364538 < baseStart_4364538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364541 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_4364541 : Nat := 118140960795 + 4364541 * 2 ^ 59
def prefixEnd_4364541 : Nat := 4983230072969 + 3 ^ 40 * 4364541 * 2
def baseEnd_4364541 : Nat := 2241107369255113446965347

theorem tailTrace_4364541 : CollatzResearch.WordTrace tailWord_4364541 prefixEnd_4364541 2241107369255113446965347 := by
  unfold tailWord_4364541
  simp only [CollatzResearch.WordTrace]
  refine ⟨159187888081020836103245477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106125258720680557402163651 159187888081020836103245477)
  ·
    refine ⟨29847729015191406769358527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159187888081020836103245477 29847729015191406769358527)
    ·
      refine ⟨44771593522787110154037791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29847729015191406769358527 44771593522787110154037791)
      ·
        refine ⟨67157390284180665231056687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44771593522787110154037791 67157390284180665231056687)
        ·
          refine ⟨100736085426270997846585031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67157390284180665231056687 100736085426270997846585031)
          ·
            refine ⟨151104128139406496769877547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100736085426270997846585031 151104128139406496769877547)
            ·
              refine ⟨226656192209109745154816321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151104128139406496769877547 226656192209109745154816321)
              ·
                refine ⟨169992144156832308866112241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226656192209109745154816321 169992144156832308866112241)
                ·
                  refine ⟨127494108117624231649584181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169992144156832308866112241 127494108117624231649584181)
                  ·
                    refine ⟨11952572636027271717148517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127494108117624231649584181 11952572636027271717148517)
                    ·
                      refine ⟨2241107369255113446965347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11952572636027271717148517 2241107369255113446965347)
                      ·
                        rfl

theorem cell23_4364541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_4364541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364541 prefixEnd_4364541 := by exact prefixLift 4364541
  have htrace : WordTrace (prefixWord ++ tailWord_4364541) baseStart_4364541 baseEnd_4364541 := by
    simpa [prefixWord, tailWord_4364541, baseEnd_4364541] using wordTrace_append hprefix tailTrace_4364541
  have hstable : (prefixWord ++ tailWord_4364541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364541).length < 2 ^ (prefixWord ++ tailWord_4364541).sum := by decide
  have hdescent : baseEnd_4364541 < baseStart_4364541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364545 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_4364545 : Nat := 118140960795 + 4364545 * 2 ^ 59
def prefixEnd_4364545 : Nat := 4983230072969 + 3 ^ 40 * 4364545 * 2
def baseEnd_4364545 : Nat := 2241109423177731431315329

theorem tailTrace_4364545 : CollatzResearch.WordTrace tailWord_4364545 prefixEnd_4364545 2241109423177731431315329 := by
  unfold tailWord_4364545
  simp only [CollatzResearch.WordTrace]
  refine ⟨159188033973006344786391089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106125355982004229857594059 159188033973006344786391089)
  ·
    refine ⟨119391025479754758589793317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159188033973006344786391089 119391025479754758589793317)
    ·
      refine ⟨22385817277454017235586247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119391025479754758589793317 22385817277454017235586247)
      ·
        refine ⟨33578725916181025853379371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22385817277454017235586247 33578725916181025853379371)
        ·
          refine ⟨50368088874271538780069057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33578725916181025853379371 50368088874271538780069057)
          ·
            refine ⟨37776066655703654085051793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50368088874271538780069057 37776066655703654085051793)
            ·
              refine ⟨28332049991777740563788845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37776066655703654085051793 28332049991777740563788845)
              ·
                refine ⟨10624518746916652711420817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28332049991777740563788845 10624518746916652711420817)
                ·
                  refine ⟨7968389060187489533565613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10624518746916652711420817 7968389060187489533565613)
                  ·
                    refine ⟨2988145897570308575087105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7968389060187489533565613 2988145897570308575087105)
                    ·
                      refine ⟨2241109423177731431315329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988145897570308575087105 2241109423177731431315329)
                      ·
                        rfl

theorem cell23_4364545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_4364545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364545 prefixEnd_4364545 := by exact prefixLift 4364545
  have htrace : WordTrace (prefixWord ++ tailWord_4364545) baseStart_4364545 baseEnd_4364545 := by
    simpa [prefixWord, tailWord_4364545, baseEnd_4364545] using wordTrace_append hprefix tailTrace_4364545
  have hstable : (prefixWord ++ tailWord_4364545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364545).length < 2 ^ (prefixWord ++ tailWord_4364545).sum := by decide
  have hdescent : baseEnd_4364545 < baseStart_4364545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364568 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 4, 4]
def baseStart_4364568 : Nat := 118140960795 + 4364568 * 2 ^ 59
def prefixEnd_4364568 : Nat := 4983230072969 + 3 ^ 40 * 4364568 * 2
def baseEnd_4364568 : Nat := 747040411077594947109241

theorem tailTrace_4364568 : CollatzResearch.WordTrace tailWord_4364568 prefixEnd_4364568 747040411077594947109241 := by
  unfold tailWord_4364568
  simp only [CollatzResearch.WordTrace]
  refine ⟨79594436425961509857239179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106125915234615346476318905 79594436425961509857239179)
  ·
    refine ⟨119391654638942264785858769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79594436425961509857239179 119391654638942264785858769)
    ·
      refine ⟨89543740979206698589394077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119391654638942264785858769 89543740979206698589394077)
      ·
        refine ⟨33578902867202511971022779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89543740979206698589394077 33578902867202511971022779)
        ·
          refine ⟨50368354300803767956534169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33578902867202511971022779 50368354300803767956534169)
          ·
            refine ⟨37776265725602825967400627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50368354300803767956534169 37776265725602825967400627)
            ·
              refine ⟨56664398588404238951100941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37776265725602825967400627 56664398588404238951100941)
              ·
                refine ⟨21249149470651589606662853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56664398588404238951100941 21249149470651589606662853)
                ·
                  refine ⟨3984215525747173051249285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21249149470651589606662853 3984215525747173051249285)
                  ·
                    refine ⟨747040411077594947109241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984215525747173051249285 747040411077594947109241)
                    ·
                      rfl

theorem cell23_4364568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_4364568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364568 prefixEnd_4364568 := by exact prefixLift 4364568
  have htrace : WordTrace (prefixWord ++ tailWord_4364568) baseStart_4364568 baseEnd_4364568 := by
    simpa [prefixWord, tailWord_4364568, baseEnd_4364568] using wordTrace_append hprefix tailTrace_4364568
  have hstable : (prefixWord ++ tailWord_4364568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364568).length < 2 ^ (prefixWord ++ tailWord_4364568).sum := by decide
  have hdescent : baseEnd_4364568 < baseStart_4364568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364571 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6]
def baseStart_4364571 : Nat := 118140960795 + 4364571 * 2 ^ 59
def prefixEnd_4364571 : Nat := 4983230072969 + 3 ^ 40 * 4364571 * 2
def baseEnd_4364571 : Nat := 2241122773674748329590209

theorem tailTrace_4364571 : CollatzResearch.WordTrace tailWord_4364571 prefixEnd_4364571 2241122773674748329590209 := by
  unfold tailWord_4364571
  simp only [CollatzResearch.WordTrace]
  refine ⟨159188982270912151226837567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106125988180608100817891711 159188982270912151226837567)
  ·
    refine ⟨238783473406368226840256351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159188982270912151226837567 238783473406368226840256351)
    ·
      refine ⟨358175210109552340260384527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238783473406368226840256351 358175210109552340260384527)
      ·
        refine ⟨537262815164328510390576791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358175210109552340260384527 537262815164328510390576791)
        ·
          refine ⟨805894222746492765585865187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537262815164328510390576791 805894222746492765585865187)
          ·
            refine ⟨1208841334119739148378797781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805894222746492765585865187 1208841334119739148378797781)
            ·
              refine ⟨28332218768431386290128073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1208841334119739148378797781 28332218768431386290128073)
              ·
                refine ⟨21249164076323539717596055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28332218768431386290128073 21249164076323539717596055)
                ·
                  refine ⟨31873746114485309576394083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21249164076323539717596055 31873746114485309576394083)
                  ·
                    refine ⟨47810619171727964364591125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31873746114485309576394083 47810619171727964364591125)
                    ·
                      refine ⟨2241122773674748329590209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47810619171727964364591125 2241122773674748329590209)
                      ·
                        rfl

theorem cell23_4364571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_4364571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364571 prefixEnd_4364571 := by exact prefixLift 4364571
  have htrace : WordTrace (prefixWord ++ tailWord_4364571) baseStart_4364571 baseEnd_4364571 := by
    simpa [prefixWord, tailWord_4364571, baseEnd_4364571] using wordTrace_append hprefix tailTrace_4364571
  have hstable : (prefixWord ++ tailWord_4364571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364571).length < 2 ^ (prefixWord ++ tailWord_4364571).sum := by decide
  have hdescent : baseEnd_4364571 < baseStart_4364571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364589 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4364589 : Nat := 118140960795 + 4364589 * 2 ^ 59
def prefixEnd_4364589 : Nat := 4983230072969 + 3 ^ 40 * 4364589 * 2
def baseEnd_4364589 : Nat := 747044005442176419721709

theorem tailTrace_4364589 : CollatzResearch.WordTrace tailWord_4364589 prefixEnd_4364589 747044005442176419721709 := by
  unfold tailWord_4364589
  simp only [CollatzResearch.WordTrace]
  refine ⟨159189638784846940300992821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106126425856564626867328547 159189638784846940300992821)
  ·
    refine ⟨14924028636079400653218077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159189638784846940300992821 14924028636079400653218077)
    ·
      refine ⟨5596510738529775244956779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14924028636079400653218077 5596510738529775244956779)
      ·
        refine ⟨8394766107794662867435169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5596510738529775244956779 8394766107794662867435169)
        ·
          refine ⟨6296074580845997150576377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8394766107794662867435169 6296074580845997150576377)
          ·
            refine ⟨4722055935634497862932283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296074580845997150576377 4722055935634497862932283)
            ·
              refine ⟨7083083903451746794398425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722055935634497862932283 7083083903451746794398425)
              ·
                refine ⟨5312312927588810095798819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083083903451746794398425 5312312927588810095798819)
                ·
                  refine ⟨7968469391383215143698229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5312312927588810095798819 7968469391383215143698229)
                  ·
                    refine ⟨747044005442176419721709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7968469391383215143698229 747044005442176419721709)
                    ·
                      rfl

theorem cell23_4364589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4364589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364589 prefixEnd_4364589 := by exact prefixLift 4364589
  have htrace : WordTrace (prefixWord ++ tailWord_4364589) baseStart_4364589 baseEnd_4364589 := by
    simpa [prefixWord, tailWord_4364589, baseEnd_4364589] using wordTrace_append hprefix tailTrace_4364589
  have hstable : (prefixWord ++ tailWord_4364589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364589).length < 2 ^ (prefixWord ++ tailWord_4364589).sum := by decide
  have hdescent : baseEnd_4364589 < baseStart_4364589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364609 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4364609 : Nat := 118140960795 + 4364609 * 2 ^ 59
def prefixEnd_4364609 : Nat := 4983230072969 + 3 ^ 40 * 4364609 * 2
def baseEnd_4364609 : Nat := 2241142285939619180915035

theorem tailTrace_4364609 : CollatzResearch.WordTrace tailWord_4364609 prefixEnd_4364609 2241142285939619180915035 := by
  unfold tailWord_4364609
  simp only [CollatzResearch.WordTrace]
  refine ⟨159190368244774483716720881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106126912163182989144480587 159190368244774483716720881)
  ·
    refine ⟨119392776183580862787540661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159190368244774483716720881 119392776183580862787540661)
    ·
      refine ⟨11193072767210705886331937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119392776183580862787540661 11193072767210705886331937)
      ·
        refine ⟨8394804575408029414748953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11193072767210705886331937 8394804575408029414748953)
        ·
          refine ⟨6296103431556022061061715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8394804575408029414748953 6296103431556022061061715)
          ·
            refine ⟨9444155147334033091592573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296103431556022061061715 9444155147334033091592573)
            ·
              refine ⟨3541558180250262409347215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9444155147334033091592573 3541558180250262409347215)
              ·
                refine ⟨5312337270375393614020823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541558180250262409347215 5312337270375393614020823)
                ·
                  refine ⟨7968505905563090421031235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5312337270375393614020823 7968505905563090421031235)
                  ·
                    refine ⟨11952758858344635631546853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7968505905563090421031235 11952758858344635631546853)
                    ·
                      refine ⟨2241142285939619180915035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11952758858344635631546853 2241142285939619180915035)
                      ·
                        rfl

theorem cell23_4364609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4364609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364609 prefixEnd_4364609 := by exact prefixLift 4364609
  have htrace : WordTrace (prefixWord ++ tailWord_4364609) baseStart_4364609 baseEnd_4364609 := by
    simpa [prefixWord, tailWord_4364609, baseEnd_4364609] using wordTrace_append hprefix tailTrace_4364609
  have hstable : (prefixWord ++ tailWord_4364609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364609).length < 2 ^ (prefixWord ++ tailWord_4364609).sum := by decide
  have hdescent : baseEnd_4364609 < baseStart_4364609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364626 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_4364626 : Nat := 118140960795 + 4364626 * 2 ^ 59
def prefixEnd_4364626 : Nat := 4983230072969 + 3 ^ 40 * 4364626 * 2
def baseEnd_4364626 : Nat := 2241151015110745614402457

theorem tailTrace_4364626 : CollatzResearch.WordTrace tailWord_4364626 prefixEnd_4364626 2241151015110745614402457 := by
  unfold tailWord_4364626
  simp only [CollatzResearch.WordTrace]
  refine ⟨39797747071428223905022433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106127325523808597080059821 39797747071428223905022433)
  ·
    refine ⟨29848310303571167928766825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39797747071428223905022433 29848310303571167928766825)
    ·
      refine ⟨22386232727678375946575119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29848310303571167928766825 22386232727678375946575119)
      ·
        refine ⟨33579349091517563919862679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22386232727678375946575119 33579349091517563919862679)
        ·
          refine ⟨50369023637276345879794019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33579349091517563919862679 50369023637276345879794019)
          ·
            refine ⟨75553535455914518819691029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50369023637276345879794019 75553535455914518819691029)
            ·
              refine ⟨3541571974495993069673017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75553535455914518819691029 3541571974495993069673017)
              ·
                refine ⟨2656178980871994802254763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541571974495993069673017 2656178980871994802254763)
                ·
                  refine ⟨3984268471307992203382145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656178980871994802254763 3984268471307992203382145)
                  ·
                    refine ⟨2988201353480994152536609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984268471307992203382145 2988201353480994152536609)
                    ·
                      refine ⟨2241151015110745614402457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988201353480994152536609 2241151015110745614402457)
                      ·
                        rfl

theorem cell23_4364626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_4364626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364626 prefixEnd_4364626 := by exact prefixLift 4364626
  have htrace : WordTrace (prefixWord ++ tailWord_4364626) baseStart_4364626 baseEnd_4364626 := by
    simpa [prefixWord, tailWord_4364626, baseEnd_4364626] using wordTrace_append hprefix tailTrace_4364626
  have hstable : (prefixWord ++ tailWord_4364626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364626).length < 2 ^ (prefixWord ++ tailWord_4364626).sum := by decide
  have hdescent : baseEnd_4364626 < baseStart_4364626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364628 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4364628 : Nat := 118140960795 + 4364628 * 2 ^ 59
def prefixEnd_4364628 : Nat := 4983230072969 + 3 ^ 40 * 4364628 * 2
def baseEnd_4364628 : Nat := 747050680690684868859149

theorem tailTrace_4364628 : CollatzResearch.WordTrace tailWord_4364628 prefixEnd_4364628 747050680690684868859149 := by
  unfold tailWord_4364628
  simp only [CollatzResearch.WordTrace]
  refine ⟨79595530615852824980831269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106127374154470433307775025 79595530615852824980831269)
  ·
    refine ⟨14924161990472404683905863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79595530615852824980831269 14924161990472404683905863)
    ·
      refine ⟨22386242985708607025858795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14924161990472404683905863 22386242985708607025858795)
      ·
        refine ⟨33579364478562910538788193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22386242985708607025858795 33579364478562910538788193)
        ·
          refine ⟨25184523358922182904091145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33579364478562910538788193 25184523358922182904091145)
          ·
            refine ⟨18888392519191637178068359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25184523358922182904091145 18888392519191637178068359)
            ·
              refine ⟨28332588778787455767102539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18888392519191637178068359 28332588778787455767102539)
              ·
                refine ⟨42498883168181183650653809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28332588778787455767102539 42498883168181183650653809)
                ·
                  refine ⟨31874162376135887737990357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42498883168181183650653809 31874162376135887737990357)
                  ·
                    refine ⟨747050680690684868859149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31874162376135887737990357 747050680690684868859149)
                    ·
                      rfl

theorem cell23_4364628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4364628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364628 prefixEnd_4364628 := by exact prefixLift 4364628
  have htrace : WordTrace (prefixWord ++ tailWord_4364628) baseStart_4364628 baseEnd_4364628 := by
    simpa [prefixWord, tailWord_4364628, baseEnd_4364628] using wordTrace_append hprefix tailTrace_4364628
  have hstable : (prefixWord ++ tailWord_4364628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364628).length < 2 ^ (prefixWord ++ tailWord_4364628).sum := by decide
  have hdescent : baseEnd_4364628 < baseStart_4364628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364642 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4364642 : Nat := 118140960795 + 4364642 * 2 ^ 59
def prefixEnd_4364642 : Nat := 4983230072969 + 3 ^ 40 * 4364642 * 2
def baseEnd_4364642 : Nat := 2241159230801217551802383

theorem tailTrace_4364642 : CollatzResearch.WordTrace tailWord_4364642 prefixEnd_4364642 2241159230801217551802383 := by
  unfold tailWord_4364642
  simp only [CollatzResearch.WordTrace]
  refine ⟨39797892963413732588168045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106127714569103286901781453 39797892963413732588168045)
  ·
    refine ⟨14924209861280149720563017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39797892963413732588168045 14924209861280149720563017)
    ·
      refine ⟨11193157395960112290422263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14924209861280149720563017 11193157395960112290422263)
      ·
        refine ⟨16789736093940168435633395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193157395960112290422263 16789736093940168435633395)
        ·
          refine ⟨25184604140910252653450093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16789736093940168435633395 25184604140910252653450093)
          ·
            refine ⟨9444226552841344745043785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25184604140910252653450093 9444226552841344745043785)
            ·
              refine ⟨7083169914631008558782839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9444226552841344745043785 7083169914631008558782839)
              ·
                refine ⟨10624754871946512838174259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7083169914631008558782839 10624754871946512838174259)
                ·
                  refine ⟨15937132307919769257261389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10624754871946512838174259 15937132307919769257261389)
                  ·
                    refine ⟨5976424615469913471473021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15937132307919769257261389 5976424615469913471473021)
                    ·
                      refine ⟨2241159230801217551802383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5976424615469913471473021 2241159230801217551802383)
                      ·
                        rfl

theorem cell23_4364642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4364642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364642 prefixEnd_4364642 := by exact prefixLift 4364642
  have htrace : WordTrace (prefixWord ++ tailWord_4364642) baseStart_4364642 baseEnd_4364642 := by
    simpa [prefixWord, tailWord_4364642, baseEnd_4364642] using wordTrace_append hprefix tailTrace_4364642
  have hstable : (prefixWord ++ tailWord_4364642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364642).length < 2 ^ (prefixWord ++ tailWord_4364642).sum := by decide
  have hdescent : baseEnd_4364642 < baseStart_4364642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364668 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_4364668 : Nat := 118140960795 + 4364668 * 2 ^ 59
def prefixEnd_4364668 : Nat := 4983230072969 + 3 ^ 40 * 4364668 * 2
def baseEnd_4364668 : Nat := 2241172581298234450077263

theorem tailTrace_4364668 : CollatzResearch.WordTrace tailWord_4364668 prefixEnd_4364668 2241172581298234450077263 := by
  unfold tailWord_4364668
  simp only [CollatzResearch.WordTrace]
  refine ⟨79596260075780368396559329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106128346767707157862079105 79596260075780368396559329)
  ·
    refine ⟨59697195056835276297419497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79596260075780368396559329 59697195056835276297419497)
    ·
      refine ⟨44772896292626457223064623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59697195056835276297419497 44772896292626457223064623)
      ·
        refine ⟨67159344438939685834596935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44772896292626457223064623 67159344438939685834596935)
        ·
          refine ⟨100739016658409528751895403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67159344438939685834596935 100739016658409528751895403)
          ·
            refine ⟨151108524987614293127843105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100739016658409528751895403 151108524987614293127843105)
            ·
              refine ⟨113331393740710719845882329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151108524987614293127843105 113331393740710719845882329)
              ·
                refine ⟨84998545305533039884411747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113331393740710719845882329 84998545305533039884411747)
                ·
                  refine ⟨127497817958299559826617621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84998545305533039884411747 127497817958299559826617621)
                  ·
                    refine ⟨5976460216795291866872701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 127497817958299559826617621 5976460216795291866872701)
                    ·
                      refine ⟨2241172581298234450077263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5976460216795291866872701 2241172581298234450077263)
                      ·
                        rfl

theorem cell23_4364668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_4364668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364668 prefixEnd_4364668 := by exact prefixLift 4364668
  have htrace : WordTrace (prefixWord ++ tailWord_4364668) baseStart_4364668 baseEnd_4364668 := by
    simpa [prefixWord, tailWord_4364668, baseEnd_4364668] using wordTrace_append hprefix tailTrace_4364668
  have hstable : (prefixWord ++ tailWord_4364668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364668).length < 2 ^ (prefixWord ++ tailWord_4364668).sum := by decide
  have hdescent : baseEnd_4364668 < baseStart_4364668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364669 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_4364669 : Nat := 118140960795 + 4364669 * 2 ^ 59
def prefixEnd_4364669 : Nat := 4983230072969 + 3 ^ 40 * 4364669 * 2
def baseEnd_4364669 : Nat := 2241173094778888946164759

theorem tailTrace_4364669 : CollatzResearch.WordTrace tailWord_4364669 prefixEnd_4364669 2241173094778888946164759 := by
  unfold tailWord_4364669
  simp only [CollatzResearch.WordTrace]
  refine ⟨159192556624557113963905061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106128371083038075975936707 159192556624557113963905061)
  ·
    refine ⟨29848604367104458868232199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159192556624557113963905061 29848604367104458868232199)
    ·
      refine ⟨44772906550656688302348299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29848604367104458868232199 44772906550656688302348299)
      ·
        refine ⟨67159359825985032453522449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44772906550656688302348299 67159359825985032453522449)
        ·
          refine ⟨50369519869488774340141837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67159359825985032453522449 50369519869488774340141837)
          ·
            refine ⟨18888569951058290377553189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50369519869488774340141837 18888569951058290377553189)
            ·
              refine ⟨3541606865823429445791223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18888569951058290377553189 3541606865823429445791223)
              ·
                refine ⟨5312410298735144168686835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541606865823429445791223 5312410298735144168686835)
                ·
                  refine ⟨7968615448102716253030253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5312410298735144168686835 7968615448102716253030253)
                  ·
                    refine ⟨2988230793038518594886345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7968615448102716253030253 2988230793038518594886345)
                    ·
                      refine ⟨2241173094778888946164759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988230793038518594886345 2241173094778888946164759)
                      ·
                        rfl

theorem cell23_4364669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_4364669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364669 prefixEnd_4364669 := by exact prefixLift 4364669
  have htrace : WordTrace (prefixWord ++ tailWord_4364669) baseStart_4364669 baseEnd_4364669 := by
    simpa [prefixWord, tailWord_4364669, baseEnd_4364669] using wordTrace_append hprefix tailTrace_4364669
  have hstable : (prefixWord ++ tailWord_4364669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364669).length < 2 ^ (prefixWord ++ tailWord_4364669).sum := by decide
  have hdescent : baseEnd_4364669 < baseStart_4364669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364728 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_4364728 : Nat := 118140960795 + 4364728 * 2 ^ 59
def prefixEnd_4364728 : Nat := 4983230072969 + 3 ^ 40 * 4364728 * 2
def baseEnd_4364728 : Nat := 2241203390137504215326987

theorem tailTrace_4364728 : CollatzResearch.WordTrace tailWord_4364728 prefixEnd_4364728 2241203390137504215326987 := by
  unfold tailWord_4364728
  simp only [CollatzResearch.WordTrace]
  refine ⟨79597354265671683520151419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106129805687562244693535225 79597354265671683520151419)
  ·
    refine ⟨119396031398507525280227129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79597354265671683520151419 119396031398507525280227129)
    ·
      refine ⟨89547023548880643960170347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119396031398507525280227129 89547023548880643960170347)
      ·
        refine ⟨134320535323320965940255521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89547023548880643960170347 134320535323320965940255521)
        ·
          refine ⟨100740401492490724455191641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134320535323320965940255521 100740401492490724455191641)
          ·
            refine ⟨75555301119368043341393731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100740401492490724455191641 75555301119368043341393731)
            ·
              refine ⟨113332951679052065012090597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75555301119368043341393731 113332951679052065012090597)
              ·
                refine ⟨21249928439822262189766987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113332951679052065012090597 21249928439822262189766987)
                ·
                  refine ⟨31874892659733393284650481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21249928439822262189766987 31874892659733393284650481)
                  ·
                    refine ⟨23906169494800044963487861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31874892659733393284650481 23906169494800044963487861)
                    ·
                      refine ⟨2241203390137504215326987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23906169494800044963487861 2241203390137504215326987)
                      ·
                        rfl

theorem cell23_4364728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_4364728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364728 prefixEnd_4364728 := by exact prefixLift 4364728
  have htrace : WordTrace (prefixWord ++ tailWord_4364728) baseStart_4364728 baseEnd_4364728 := by
    simpa [prefixWord, tailWord_4364728, baseEnd_4364728] using wordTrace_append hprefix tailTrace_4364728
  have hstable : (prefixWord ++ tailWord_4364728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364728).length < 2 ^ (prefixWord ++ tailWord_4364728).sum := by decide
  have hdescent : baseEnd_4364728 < baseStart_4364728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 8, 4, 2]
def baseStart_4364755 : Nat := 118140960795 + 4364755 * 2 ^ 59
def prefixEnd_4364755 : Nat := 4983230072969 + 3 ^ 40 * 4364755 * 2
def baseEnd_4364755 : Nat := 2241217254115175609689363

theorem tailTrace_4364755 : CollatzResearch.WordTrace tailWord_4364755 prefixEnd_4364755 2241217254115175609689363 := by
  unfold tailWord_4364755
  simp only [CollatzResearch.WordTrace]
  refine ⟨159195693302245550651535719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106130462201497033767690479 159195693302245550651535719)
  ·
    refine ⟨238793539953368325977303579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159195693302245550651535719 238793539953368325977303579)
    ·
      refine ⟨358190309930052488965955369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238793539953368325977303579 358190309930052488965955369)
      ·
        refine ⟨268642732447539366724466527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358190309930052488965955369 268642732447539366724466527)
        ·
          refine ⟨402964098671309050086699791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268642732447539366724466527 402964098671309050086699791)
          ·
            refine ⟨604446148006963575130049687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402964098671309050086699791 604446148006963575130049687)
            ·
              refine ⟨906669222010445362695074531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604446148006963575130049687 906669222010445362695074531)
              ·
                refine ⟨1360003833015668044042611797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906669222010445362695074531 1360003833015668044042611797)
                ·
                  refine ⟨15937544918152359891124357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1360003833015668044042611797 15937544918152359891124357)
                  ·
                    refine ⟨2988289672153567479585817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15937544918152359891124357 2988289672153567479585817)
                    ·
                      refine ⟨2241217254115175609689363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988289672153567479585817 2241217254115175609689363)
                      ·
                        rfl

theorem cell23_4364755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4, 2].length) (baseStart_4364755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364755 prefixEnd_4364755 := by exact prefixLift 4364755
  have htrace : WordTrace (prefixWord ++ tailWord_4364755) baseStart_4364755 baseEnd_4364755 := by
    simpa [prefixWord, tailWord_4364755, baseEnd_4364755] using wordTrace_append hprefix tailTrace_4364755
  have hstable : (prefixWord ++ tailWord_4364755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364755).length < 2 ^ (prefixWord ++ tailWord_4364755).sum := by decide
  have hdescent : baseEnd_4364755 < baseStart_4364755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364846 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_4364846 : Nat := 118140960795 + 4364846 * 2 ^ 59
def prefixEnd_4364846 : Nat := 4983230072969 + 3 ^ 40 * 4364846 * 2
def baseEnd_4364846 : Nat := 249029331206081639294605

theorem tailTrace_4364846 : CollatzResearch.WordTrace tailWord_4364846 prefixEnd_4364846 249029331206081639294605 := by
  unfold tailWord_4364846
  simp only [CollatzResearch.WordTrace]
  refine ⟨19899876543114484149137299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106132674896610582128732261 19899876543114484149137299)
  ·
    refine ⟨29849814814671726223705949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19899876543114484149137299 29849814814671726223705949)
    ·
      refine ⟨11193680555501897333889731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29849814814671726223705949 11193680555501897333889731)
      ·
        refine ⟨16790520833252846000834597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193680555501897333889731 16790520833252846000834597)
        ·
          refine ⟨3148222656234908625156487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16790520833252846000834597 3148222656234908625156487)
          ·
            refine ⟨4722333984352362937734731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148222656234908625156487 4722333984352362937734731)
            ·
              refine ⟨7083500976528544406602097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722333984352362937734731 7083500976528544406602097)
              ·
                refine ⟨5312625732396408304951573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083500976528544406602097 5312625732396408304951573)
                ·
                  refine ⟨249029331206081639294605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5312625732396408304951573 249029331206081639294605)
                  ·
                    rfl

theorem cell23_4364846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_4364846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364846 prefixEnd_4364846 := by exact prefixLift 4364846
  have htrace : WordTrace (prefixWord ++ tailWord_4364846) baseStart_4364846 baseEnd_4364846 := by
    simpa [prefixWord, tailWord_4364846, baseEnd_4364846] using wordTrace_append hprefix tailTrace_4364846
  have hstable : (prefixWord ++ tailWord_4364846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364846).length < 2 ^ (prefixWord ++ tailWord_4364846).sum := by decide
  have hdescent : baseEnd_4364846 < baseStart_4364846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364872 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 2, 4]
def baseStart_4364872 : Nat := 118140960795 + 4364872 * 2 ^ 59
def prefixEnd_4364872 : Nat := 4983230072969 + 3 ^ 40 * 4364872 * 2
def baseEnd_4364872 : Nat := 747092443783917217308775

theorem tailTrace_4364872 : CollatzResearch.WordTrace tailWord_4364872 prefixEnd_4364872 747092443783917217308775 := by
  unfold tailWord_4364872
  simp only [CollatzResearch.WordTrace]
  refine ⟨79599980321410839816772435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106133307095214453089029913 79599980321410839816772435)
  ·
    refine ⟨119399970482116259725158653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79599980321410839816772435 119399970482116259725158653)
    ·
      refine ⟨44774988930793597396934495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119399970482116259725158653 44774988930793597396934495)
      ·
        refine ⟨67162483396190396095401743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44774988930793597396934495 67162483396190396095401743)
        ·
          refine ⟨100743725094285594143102615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67162483396190396095401743 100743725094285594143102615)
          ·
            refine ⟨151115587641428391214653923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100743725094285594143102615 151115587641428391214653923)
            ·
              refine ⟨226673381462142586821980885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151115587641428391214653923 226673381462142586821980885)
              ·
                refine ⟨5312657378018966878640177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226673381462142586821980885 5312657378018966878640177)
                ·
                  refine ⟨3984493033514225158980133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5312657378018966878640177 3984493033514225158980133)
                  ·
                    refine ⟨747092443783917217308775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984493033514225158980133 747092443783917217308775)
                    ·
                      rfl

theorem cell23_4364872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_4364872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364872 prefixEnd_4364872 := by exact prefixLift 4364872
  have htrace : WordTrace (prefixWord ++ tailWord_4364872) baseStart_4364872 baseEnd_4364872 := by
    simpa [prefixWord, tailWord_4364872, baseEnd_4364872] using wordTrace_append hprefix tailTrace_4364872
  have hstable : (prefixWord ++ tailWord_4364872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364872).length < 2 ^ (prefixWord ++ tailWord_4364872).sum := by decide
  have hdescent : baseEnd_4364872 < baseStart_4364872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364879 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 3, 2, 2]
def baseStart_4364879 : Nat := 118140960795 + 4364879 * 2 ^ 59
def prefixEnd_4364879 : Nat := 4983230072969 + 3 ^ 40 * 4364879 * 2
def baseEnd_4364879 : Nat := 2241280925716333124538793

theorem tailTrace_4364879 : CollatzResearch.WordTrace tailWord_4364879 prefixEnd_4364879 2241280925716333124538793 := by
  unfold tailWord_4364879
  simp only [CollatzResearch.WordTrace]
  refine ⟨159200215953796319829049691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106133477302530879886033127 159200215953796319829049691)
  ·
    refine ⟨238800323930694479743574537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159200215953796319829049691 238800323930694479743574537)
    ·
      refine ⟨179100242948020859807680903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238800323930694479743574537 179100242948020859807680903)
      ·
        refine ⟨268650364422031289711521355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179100242948020859807680903 268650364422031289711521355)
        ·
          refine ⟨402975546633046934567282033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268650364422031289711521355 402975546633046934567282033)
          ·
            refine ⟨302231659974785200925461525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402975546633046934567282033 302231659974785200925461525)
            ·
              refine ⟨14167109061318056293381009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 302231659974785200925461525 14167109061318056293381009)
              ·
                refine ⟨10625331795988542220035757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14167109061318056293381009 10625331795988542220035757)
                ·
                  refine ⟨3984499423495703332513409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10625331795988542220035757 3984499423495703332513409)
                  ·
                    refine ⟨2988374567621777499385057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984499423495703332513409 2988374567621777499385057)
                    ·
                      refine ⟨2241280925716333124538793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988374567621777499385057 2241280925716333124538793)
                      ·
                        rfl

theorem cell23_4364879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 2, 2].length) (baseStart_4364879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364879 prefixEnd_4364879 := by exact prefixLift 4364879
  have htrace : WordTrace (prefixWord ++ tailWord_4364879) baseStart_4364879 baseEnd_4364879 := by
    simpa [prefixWord, tailWord_4364879, baseEnd_4364879] using wordTrace_append hprefix tailTrace_4364879
  have hstable : (prefixWord ++ tailWord_4364879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364879).length < 2 ^ (prefixWord ++ tailWord_4364879).sum := by decide
  have hdescent : baseEnd_4364879 < baseStart_4364879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364939 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 1, 3, 2]
def baseStart_4364939 : Nat := 118140960795 + 4364939 * 2 ^ 59
def prefixEnd_4364939 : Nat := 4983230072969 + 3 ^ 40 * 4364939 * 2
def baseEnd_4364939 : Nat := 2241311734555602889788517

theorem tailTrace_4364939 : CollatzResearch.WordTrace tailWord_4364939 prefixEnd_4364939 2241311734555602889788517 := by
  unfold tailWord_4364939
  simp only [CollatzResearch.WordTrace]
  refine ⟨159202404333578950076233871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106134936222385966717489247 159202404333578950076233871)
  ·
    refine ⟨238803606500368425114350807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159202404333578950076233871 238803606500368425114350807)
    ·
      refine ⟨358205409750552637671526211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238803606500368425114350807 358205409750552637671526211)
      ·
        refine ⟨537308114625828956507289317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358205409750552637671526211 537308114625828956507289317)
        ·
          refine ⟨100745271492342929345116747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 537308114625828956507289317 100745271492342929345116747)
          ·
            refine ⟨151117907238514394017675121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100745271492342929345116747 151117907238514394017675121)
            ·
              refine ⟨113338430428885795513256341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151117907238514394017675121 113338430428885795513256341)
              ·
                refine ⟨5312738926354021664683891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113338430428885795513256341 5312738926354021664683891)
                ·
                  refine ⟨7969108389531032497025837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5312738926354021664683891 7969108389531032497025837)
                  ·
                    refine ⟨2988415646074137186384689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7969108389531032497025837 2988415646074137186384689)
                    ·
                      refine ⟨2241311734555602889788517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988415646074137186384689 2241311734555602889788517)
                      ·
                        rfl

theorem cell23_4364939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 3, 2].length) (baseStart_4364939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364939 prefixEnd_4364939 := by exact prefixLift 4364939
  have htrace : WordTrace (prefixWord ++ tailWord_4364939) baseStart_4364939 baseEnd_4364939 := by
    simpa [prefixWord, tailWord_4364939, baseEnd_4364939] using wordTrace_append hprefix tailTrace_4364939
  have hstable : (prefixWord ++ tailWord_4364939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364939).length < 2 ^ (prefixWord ++ tailWord_4364939).sum := by decide
  have hdescent : baseEnd_4364939 < baseStart_4364939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364965 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_4364965 : Nat := 118140960795 + 4364965 * 2 ^ 59
def prefixEnd_4364965 : Nat := 4983230072969 + 3 ^ 40 * 4364965 * 2
def baseEnd_4364965 : Nat := 2241325085052619788063397

theorem tailTrace_4364965 : CollatzResearch.WordTrace tailWord_4364965 prefixEnd_4364965 2241325085052619788063397 := by
  unfold tailWord_4364965
  simp only [CollatzResearch.WordTrace]
  refine ⟨159203352631484756516680349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106135568420989837677786899 159203352631484756516680349)
  ·
    refine ⟨59701257236806783693755131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159203352631484756516680349 59701257236806783693755131)
    ·
      refine ⟨89551885855210175540632697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59701257236806783693755131 89551885855210175540632697)
      ·
        refine ⟨67163914391407631655474523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89551885855210175540632697 67163914391407631655474523)
        ·
          refine ⟨100745871587111447483211785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67163914391407631655474523 100745871587111447483211785)
          ·
            refine ⟨75559403690333585612408839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100745871587111447483211785 75559403690333585612408839)
            ·
              refine ⟨113339105535500378418613259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75559403690333585612408839 113339105535500378418613259)
              ·
                refine ⟨170008658303250567627919889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113339105535500378418613259 170008658303250567627919889)
                ·
                  refine ⟨127506493727437925720939917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170008658303250567627919889 127506493727437925720939917)
                  ·
                    refine ⟨47814935147789222145352469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127506493727437925720939917 47814935147789222145352469)
                    ·
                      refine ⟨2241325085052619788063397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47814935147789222145352469 2241325085052619788063397)
                      ·
                        rfl

theorem cell23_4364965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_4364965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364965 prefixEnd_4364965 := by exact prefixLift 4364965
  have htrace : WordTrace (prefixWord ++ tailWord_4364965) baseStart_4364965 baseEnd_4364965 := by
    simpa [prefixWord, tailWord_4364965, baseEnd_4364965] using wordTrace_append hprefix tailTrace_4364965
  have hstable : (prefixWord ++ tailWord_4364965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364965).length < 2 ^ (prefixWord ++ tailWord_4364965).sum := by decide
  have hdescent : baseEnd_4364965 < baseStart_4364965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364986 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_4364986 : Nat := 118140960795 + 4364986 * 2 ^ 59
def prefixEnd_4364986 : Nat := 4983230072969 + 3 ^ 40 * 4364986 * 2
def baseEnd_4364986 : Nat := 2241335868146364205900801

theorem tailTrace_4364986 : CollatzResearch.WordTrace tailWord_4364986 prefixEnd_4364986 2241335868146364205900801 := by
  unfold tailWord_4364986
  simp only [CollatzResearch.WordTrace]
  refine ⟨39801029641102169275798703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106136079042939118068796541 39801029641102169275798703)
  ·
    refine ⟨59701544461653253913698055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39801029641102169275798703 59701544461653253913698055)
    ·
      refine ⟨89552316692479880870547083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59701544461653253913698055 89552316692479880870547083)
      ·
        refine ⟨134328475038719821305820625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89552316692479880870547083 134328475038719821305820625)
        ·
          refine ⟨100746356279039865979365469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134328475038719821305820625 100746356279039865979365469)
          ·
            refine ⟨37779883604639949742262051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100746356279039865979365469 37779883604639949742262051)
            ·
              refine ⟨56669825406959924613393077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37779883604639949742262051 56669825406959924613393077)
              ·
                refine ⟨5312796131902492932505601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56669825406959924613393077 5312796131902492932505601)
                ·
                  refine ⟨3984597098926869699379201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5312796131902492932505601 3984597098926869699379201)
                  ·
                    refine ⟨2988447824195152274534401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984597098926869699379201 2988447824195152274534401)
                    ·
                      refine ⟨2241335868146364205900801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988447824195152274534401 2241335868146364205900801)
                      ·
                        rfl

theorem cell23_4364986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_4364986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364986 prefixEnd_4364986 := by exact prefixLift 4364986
  have htrace : WordTrace (prefixWord ++ tailWord_4364986) baseStart_4364986 baseEnd_4364986 := by
    simpa [prefixWord, tailWord_4364986, baseEnd_4364986] using wordTrace_append hprefix tailTrace_4364986
  have hstable : (prefixWord ++ tailWord_4364986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364986).length < 2 ^ (prefixWord ++ tailWord_4364986).sum := by decide
  have hdescent : baseEnd_4364986 < baseStart_4364986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4364992 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 7]
def baseStart_4364992 : Nat := 118140960795 + 4364992 * 2 ^ 59
def prefixEnd_4364992 : Nat := 4983230072969 + 3 ^ 40 * 4364992 * 2
def baseEnd_4364992 : Nat := 249037661003365686936197

theorem tailTrace_4364992 : CollatzResearch.WordTrace tailWord_4364992 prefixEnd_4364992 249037661003365686936197 := by
  unfold tailWord_4364992
  simp only [CollatzResearch.WordTrace]
  refine ⟨79602168701193470063956615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106136224934924626751942153 79602168701193470063956615)
  ·
    refine ⟨119403253051790205095934923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79602168701193470063956615 119403253051790205095934923)
    ·
      refine ⟨179104879577685307643902385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119403253051790205095934923 179104879577685307643902385)
      ·
        refine ⟨134328659683263980732926789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179104879577685307643902385 134328659683263980732926789)
        ·
          refine ⟨25186623690611996387423773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134328659683263980732926789 25186623690611996387423773)
          ·
            refine ⟨9444983883979498645283915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25186623690611996387423773 9444983883979498645283915)
            ·
              refine ⟨14167475825969247967925873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9444983883979498645283915 14167475825969247967925873)
              ·
                refine ⟨10625606869476935975944405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14167475825969247967925873 10625606869476935975944405)
                ·
                  refine ⟨249037661003365686936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10625606869476935975944405 249037661003365686936197)
                  ·
                    rfl

theorem cell23_4364992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_4364992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4364992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4364992 prefixEnd_4364992 := by exact prefixLift 4364992
  have htrace : WordTrace (prefixWord ++ tailWord_4364992) baseStart_4364992 baseEnd_4364992 := by
    simpa [prefixWord, tailWord_4364992, baseEnd_4364992] using wordTrace_append hprefix tailTrace_4364992
  have hstable : (prefixWord ++ tailWord_4364992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4364992).length < 2 ^ (prefixWord ++ tailWord_4364992).sum := by decide
  have hdescent : baseEnd_4364992 < baseStart_4364992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4364992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365009 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 5]
def baseStart_4365009 : Nat := 118140960795 + 4365009 * 2 ^ 59
def prefixEnd_4365009 : Nat := 4983230072969 + 3 ^ 40 * 4365009 * 2
def baseEnd_4365009 : Nat := 249038630911268623990355

theorem tailTrace_4365009 : CollatzResearch.WordTrace tailWord_4365009 prefixEnd_4365009 249038630911268623990355 := by
  unfold tailWord_4365009
  simp only [CollatzResearch.WordTrace]
  refine ⟨159204957443325352031282081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106136638295550234687521387 159204957443325352031282081)
  ·
    refine ⟨119403718082494014023461561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159204957443325352031282081 119403718082494014023461561)
    ·
      refine ⟨89552788561870510517596171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119403718082494014023461561 89552788561870510517596171)
      ·
        refine ⟨134329182842805765776394257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89552788561870510517596171 134329182842805765776394257)
        ·
          refine ⟨100746887132104324332295693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134329182842805765776394257 100746887132104324332295693)
          ·
            refine ⟨37780082674539121624610885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100746887132104324332295693 37780082674539121624610885)
            ·
              refine ⟨7083765501476085304614541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37780082674539121624610885 7083765501476085304614541)
              ·
                refine ⟨2656412063053531989230453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7083765501476085304614541 2656412063053531989230453)
                ·
                  refine ⟨249038630911268623990355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656412063053531989230453 249038630911268623990355)
                  ·
                    rfl

theorem cell23_4365009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 5].length) (baseStart_4365009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365009 prefixEnd_4365009 := by exact prefixLift 4365009
  have htrace : WordTrace (prefixWord ++ tailWord_4365009) baseStart_4365009 baseEnd_4365009 := by
    simpa [prefixWord, tailWord_4365009, baseEnd_4365009] using wordTrace_append hprefix tailTrace_4365009
  have hstable : (prefixWord ++ tailWord_4365009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365009).length < 2 ^ (prefixWord ++ tailWord_4365009).sum := by decide
  have hdescent : baseEnd_4365009 < baseStart_4365009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365020 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4365020 : Nat := 118140960795 + 4365020 * 2 ^ 59
def prefixEnd_4365020 : Nat := 4983230072969 + 3 ^ 40 * 4365020 * 2
def baseEnd_4365020 : Nat := 2241353326488617072875645

theorem tailTrace_4365020 : CollatzResearch.WordTrace tailWord_4365020 prefixEnd_4365020 2241353326488617072875645 := by
  unfold tailWord_4365020
  simp only [CollatzResearch.WordTrace]
  refine ⟨79602679323142750454966257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106136905764190333939955009 79602679323142750454966257)
  ·
    refine ⟨59702009492357062841224693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79602679323142750454966257 59702009492357062841224693)
    ·
      refine ⟨5597063389908474641364815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59702009492357062841224693 5597063389908474641364815)
      ·
        refine ⟨8395595084862711962047223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597063389908474641364815 8395595084862711962047223)
        ·
          refine ⟨12593392627294067943070835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8395595084862711962047223 12593392627294067943070835)
          ·
            refine ⟨18890088940941101914606253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12593392627294067943070835 18890088940941101914606253)
            ·
              refine ⟨7083783352852913217977345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18890088940941101914606253 7083783352852913217977345)
              ·
                refine ⟨5312837514639684913483009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083783352852913217977345 5312837514639684913483009)
                ·
                  refine ⟨3984628135979763685112257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5312837514639684913483009 3984628135979763685112257)
                  ·
                    refine ⟨2988471101984822763834193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3984628135979763685112257 2988471101984822763834193)
                    ·
                      refine ⟨2241353326488617072875645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988471101984822763834193 2241353326488617072875645)
                      ·
                        rfl

theorem cell23_4365020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4365020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365020 prefixEnd_4365020 := by exact prefixLift 4365020
  have htrace : WordTrace (prefixWord ++ tailWord_4365020) baseStart_4365020 baseEnd_4365020 := by
    simpa [prefixWord, tailWord_4365020, baseEnd_4365020] using wordTrace_append hprefix tailTrace_4365020
  have hstable : (prefixWord ++ tailWord_4365020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365020).length < 2 ^ (prefixWord ++ tailWord_4365020).sum := by decide
  have hdescent : baseEnd_4365020 < baseStart_4365020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365082 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 8]
def baseStart_4365082 : Nat := 118140960795 + 4365082 * 2 ^ 59
def prefixEnd_4365082 : Nat := 4983230072969 + 3 ^ 40 * 4365082 * 2
def baseEnd_4365082 : Nat := 249042795809910647811151

theorem tailTrace_4365082 : CollatzResearch.WordTrace tailWord_4365082 prefixEnd_4365082 249042795809910647811151 := by
  unfold tailWord_4365082
  simp only [CollatzResearch.WordTrace]
  refine ⟨39801904993015221374672375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106138413314707256999126333 39801904993015221374672375)
  ·
    refine ⟨59702857489522832062008563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39801904993015221374672375 59702857489522832062008563)
    ·
      refine ⟨89554286234284248093012845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59702857489522832062008563 89554286234284248093012845)
      ·
        refine ⟨33582857337856593034879817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89554286234284248093012845 33582857337856593034879817)
        ·
          refine ⟨25187143003392444776159863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33582857337856593034879817 25187143003392444776159863)
          ·
            refine ⟨37780714505088667164239795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25187143003392444776159863 37780714505088667164239795)
            ·
              refine ⟨56671071757633000746359693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37780714505088667164239795 56671071757633000746359693)
              ·
                refine ⟨21251651909112375279884885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56671071757633000746359693 21251651909112375279884885)
                ·
                  refine ⟨249042795809910647811151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21251651909112375279884885 249042795809910647811151)
                  ·
                    rfl

theorem cell23_4365082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_4365082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365082 prefixEnd_4365082 := by exact prefixLift 4365082
  have htrace : WordTrace (prefixWord ++ tailWord_4365082) baseStart_4365082 baseEnd_4365082 := by
    simpa [prefixWord, tailWord_4365082, baseEnd_4365082] using wordTrace_append hprefix tailTrace_4365082
  have hstable : (prefixWord ++ tailWord_4365082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365082).length < 2 ^ (prefixWord ++ tailWord_4365082).sum := by decide
  have hdescent : baseEnd_4365082 < baseStart_4365082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365133 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 6]
def baseStart_4365133 : Nat := 118140960795 + 4365133 * 2 ^ 59
def prefixEnd_4365133 : Nat := 4983230072969 + 3 ^ 40 * 4365133 * 2
def baseEnd_4365133 : Nat := 249045705533619458973625

theorem tailTrace_4365133 : CollatzResearch.WordTrace tailWord_4365133 prefixEnd_4365133 249045705533619458973625 := by
  unfold tailWord_4365133
  simp only [CollatzResearch.WordTrace]
  refine ⟨159209480094876121208796053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106139653396584080805864035 159209480094876121208796053)
  ·
    refine ⟨7462944379447318181662315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159209480094876121208796053 7462944379447318181662315)
    ·
      refine ⟨11194416569170977272493473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7462944379447318181662315 11194416569170977272493473)
      ·
        refine ⟨8395812426878232954370105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194416569170977272493473 8395812426878232954370105)
        ·
          refine ⟨6296859320158674715777579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395812426878232954370105 6296859320158674715777579)
          ·
            refine ⟨9445288980238012073666369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296859320158674715777579 9445288980238012073666369)
            ·
              refine ⟨7083966735178509055249777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9445288980238012073666369 7083966735178509055249777)
              ·
                refine ⟨5312975051383881791437333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083966735178509055249777 5312975051383881791437333)
                ·
                  refine ⟨249045705533619458973625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5312975051383881791437333 249045705533619458973625)
                  ·
                    rfl

theorem cell23_4365133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_4365133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365133 prefixEnd_4365133 := by exact prefixLift 4365133
  have htrace : WordTrace (prefixWord ++ tailWord_4365133) baseStart_4365133 baseEnd_4365133 := by
    simpa [prefixWord, tailWord_4365133, baseEnd_4365133] using wordTrace_append hprefix tailTrace_4365133
  have hstable : (prefixWord ++ tailWord_4365133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365133).length < 2 ^ (prefixWord ++ tailWord_4365133).sum := by decide
  have hdescent : baseEnd_4365133 < baseStart_4365133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365136 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2]
def baseStart_4365136 : Nat := 118140960795 + 4365136 * 2 ^ 59
def prefixEnd_4365136 : Nat := 4983230072969 + 3 ^ 40 * 4365136 * 2
def baseEnd_4365136 : Nat := 2241412890244538619025111

theorem tailTrace_4365136 : CollatzResearch.WordTrace tailWord_4365136 prefixEnd_4365136 2241412890244538619025111 := by
  unfold tailWord_4365136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79604794756932626360577631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106139726342576835147436841 79604794756932626360577631)
  ·
    refine ⟨119407192135398939540866447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79604794756932626360577631 119407192135398939540866447)
    ·
      refine ⟨179110788203098409311299671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119407192135398939540866447 179110788203098409311299671)
      ·
        refine ⟨268666182304647613966949507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179110788203098409311299671 268666182304647613966949507)
        ·
          refine ⟨402999273456971420950424261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268666182304647613966949507 402999273456971420950424261)
          ·
            refine ⟨75562363773182141428204549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 402999273456971420950424261 75562363773182141428204549)
            ·
              refine ⟨14167943207471651517788353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75562363773182141428204549 14167943207471651517788353)
              ·
                refine ⟨10625957405603738638341265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14167943207471651517788353 10625957405603738638341265)
                ·
                  refine ⟨7969468054202803978755949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10625957405603738638341265 7969468054202803978755949)
                  ·
                    refine ⟨2988550520326051492033481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7969468054202803978755949 2988550520326051492033481)
                    ·
                      refine ⟨2241412890244538619025111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988550520326051492033481 2241412890244538619025111)
                      ·
                        rfl

theorem cell23_4365136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 3, 2].length) (baseStart_4365136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365136 prefixEnd_4365136 := by exact prefixLift 4365136
  have htrace : WordTrace (prefixWord ++ tailWord_4365136) baseStart_4365136 baseEnd_4365136 := by
    simpa [prefixWord, tailWord_4365136, baseEnd_4365136] using wordTrace_append hprefix tailTrace_4365136
  have hstable : (prefixWord ++ tailWord_4365136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365136).length < 2 ^ (prefixWord ++ tailWord_4365136).sum := by decide
  have hdescent : baseEnd_4365136 < baseStart_4365136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365137 : List Nat := [1, 2, 2, 1, 7, 1, 2, 2, 1, 4]
def baseStart_4365137 : Nat := 118140960795 + 4365137 * 2 ^ 59
def prefixEnd_4365137 : Nat := 4983230072969 + 3 ^ 40 * 4365137 * 2
def baseEnd_4365137 : Nat := 747137801241731038370869

theorem tailTrace_4365137 : CollatzResearch.WordTrace tailWord_4365137 prefixEnd_4365137 747137801241731038370869 := by
  unfold tailWord_4365137
  simp only [CollatzResearch.WordTrace]
  refine ⟨159209625986861629891941665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106139750657907753261294443 159209625986861629891941665)
  ·
    refine ⟨119407219490146222418956249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159209625986861629891941665 119407219490146222418956249)
    ·
      refine ⟨89555414617609666814217187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119407219490146222418956249 89555414617609666814217187)
      ·
        refine ⟨134333121926414500221325781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89555414617609666814217187 134333121926414500221325781)
        ·
          refine ⟨3148432545150339848937323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 134333121926414500221325781 3148432545150339848937323)
          ·
            refine ⟨4722648817725509773405985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148432545150339848937323 4722648817725509773405985)
            ·
              refine ⟨3541986613294132330054489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722648817725509773405985 3541986613294132330054489)
              ·
                refine ⟨2656489959970599247540867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541986613294132330054489 2656489959970599247540867)
                ·
                  refine ⟨3984734939955898871311301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656489959970599247540867 3984734939955898871311301)
                  ·
                    refine ⟨747137801241731038370869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984734939955898871311301 747137801241731038370869)
                    ·
                      rfl

theorem cell23_4365137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_4365137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365137 prefixEnd_4365137 := by exact prefixLift 4365137
  have htrace : WordTrace (prefixWord ++ tailWord_4365137) baseStart_4365137 baseEnd_4365137 := by
    simpa [prefixWord, tailWord_4365137, baseEnd_4365137] using wordTrace_append hprefix tailTrace_4365137
  have hstable : (prefixWord ++ tailWord_4365137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365137).length < 2 ^ (prefixWord ++ tailWord_4365137).sum := by decide
  have hdescent : baseEnd_4365137 < baseStart_4365137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365159 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 1, 6]
def baseStart_4365159 : Nat := 118140960795 + 4365159 * 2 ^ 59
def prefixEnd_4365159 : Nat := 4983230072969 + 3 ^ 40 * 4365159 * 2
def baseEnd_4365159 : Nat := 747141566766530676345835

theorem tailTrace_4365159 : CollatzResearch.WordTrace tailWord_4365159 prefixEnd_4365159 747141566766530676345835 := by
  unfold tailWord_4365159
  simp only [CollatzResearch.WordTrace]
  refine ⟨159210428392781927649242531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106140285595187951766161687 159210428392781927649242531)
  ·
    refine ⟨238815642589172891473863797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159210428392781927649242531 238815642589172891473863797)
    ·
      refine ⟨22388966492734958575674731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238815642589172891473863797 22388966492734958575674731)
      ·
        refine ⟨33583449739102437863512097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22388966492734958575674731 33583449739102437863512097)
        ·
          refine ⟨25187587304326828397634073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33583449739102437863512097 25187587304326828397634073)
          ·
            refine ⟨18890690478245121298225555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25187587304326828397634073 18890690478245121298225555)
            ·
              refine ⟨28336035717367681947338333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18890690478245121298225555 28336035717367681947338333)
              ·
                refine ⟨10626013394012880730251875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28336035717367681947338333 10626013394012880730251875)
                ·
                  refine ⟨15939020091019321095377813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626013394012880730251875 15939020091019321095377813)
                  ·
                    refine ⟨747141566766530676345835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15939020091019321095377813 747141566766530676345835)
                    ·
                      rfl

theorem cell23_4365159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_4365159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365159 prefixEnd_4365159 := by exact prefixLift 4365159
  have htrace : WordTrace (prefixWord ++ tailWord_4365159) baseStart_4365159 baseEnd_4365159 := by
    simpa [prefixWord, tailWord_4365159, baseEnd_4365159] using wordTrace_append hprefix tailTrace_4365159
  have hstable : (prefixWord ++ tailWord_4365159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365159).length < 2 ^ (prefixWord ++ tailWord_4365159).sum := by decide
  have hdescent : baseEnd_4365159 < baseStart_4365159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365179 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4]
def baseStart_4365179 : Nat := 118140960795 + 4365179 * 2 ^ 59
def prefixEnd_4365179 : Nat := 4983230072969 + 3 ^ 40 * 4365179 * 2
def baseEnd_4365179 : Nat := 2241434969912681950787413

theorem tailTrace_4365179 : CollatzResearch.WordTrace tailWord_4365179 prefixEnd_4365179 2241434969912681950787413 := by
  unfold tailWord_4365179
  simp only [CollatzResearch.WordTrace]
  refine ⟨159211157852709471064970591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106140771901806314043313727 159211157852709471064970591)
  ·
    refine ⟨238816736779064206597455887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159211157852709471064970591 238816736779064206597455887)
    ·
      refine ⟨358225105168596309896183831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238816736779064206597455887 358225105168596309896183831)
      ·
        refine ⟨537337657752894464844275747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358225105168596309896183831 537337657752894464844275747)
        ·
          refine ⟨806006486629341697266413621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537337657752894464844275747 806006486629341697266413621)
          ·
            refine ⟨75563108121500784118726277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 806006486629341697266413621 75563108121500784118726277)
            ·
              refine ⟨14168082772781397022261177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75563108121500784118726277 14168082772781397022261177)
              ·
                refine ⟨10626062079586047766695883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14168082772781397022261177 10626062079586047766695883)
                ·
                  refine ⟨15939093119379071650043825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626062079586047766695883 15939093119379071650043825)
                  ·
                    refine ⟨11954319839534303737532869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15939093119379071650043825 11954319839534303737532869)
                    ·
                      refine ⟨2241434969912681950787413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11954319839534303737532869 2241434969912681950787413)
                      ·
                        rfl

theorem cell23_4365179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_4365179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365179 prefixEnd_4365179 := by exact prefixLift 4365179
  have htrace : WordTrace (prefixWord ++ tailWord_4365179) baseStart_4365179 baseEnd_4365179 := by
    simpa [prefixWord, tailWord_4365179, baseEnd_4365179] using wordTrace_append hprefix tailTrace_4365179
  have hstable : (prefixWord ++ tailWord_4365179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365179).length < 2 ^ (prefixWord ++ tailWord_4365179).sum := by decide
  have hdescent : baseEnd_4365179 < baseStart_4365179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365193 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_4365193 : Nat := 118140960795 + 4365193 * 2 ^ 59
def prefixEnd_4365193 : Nat := 4983230072969 + 3 ^ 40 * 4365193 * 2
def baseEnd_4365193 : Nat := 747147386213948298670783

theorem tailTrace_4365193 : CollatzResearch.WordTrace tailWord_4365193 prefixEnd_4365193 747147386213948298670783 := by
  unfold tailWord_4365193
  simp only [CollatzResearch.WordTrace]
  refine ⟨159211668474658751455980233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106141112316439167637320155 159211668474658751455980233)
  ·
    refine ⟨119408751355994063591985175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159211668474658751455980233 119408751355994063591985175)
    ·
      refine ⟨179113127033991095387977763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119408751355994063591985175 179113127033991095387977763)
      ·
        refine ⟨268669690550986643081966645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179113127033991095387977763 268669690550986643081966645)
        ·
          refine ⟨25187783489154997788934373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 268669690550986643081966645 25187783489154997788934373)
          ·
            refine ⟨4722709404216562085425195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25187783489154997788934373 4722709404216562085425195)
            ·
              refine ⟨7084064106324843128137793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722709404216562085425195 7084064106324843128137793)
              ·
                refine ⟨5313048079743632346103345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084064106324843128137793 5313048079743632346103345)
                ·
                  refine ⟨3984786059807724259577509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313048079743632346103345 3984786059807724259577509)
                  ·
                    refine ⟨747147386213948298670783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984786059807724259577509 747147386213948298670783)
                    ·
                      rfl

theorem cell23_4365193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_4365193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365193 prefixEnd_4365193 := by exact prefixLift 4365193
  have htrace : WordTrace (prefixWord ++ tailWord_4365193) baseStart_4365193 baseEnd_4365193 := by
    simpa [prefixWord, tailWord_4365193, baseEnd_4365193] using wordTrace_append hprefix tailTrace_4365193
  have hstable : (prefixWord ++ tailWord_4365193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365193).length < 2 ^ (prefixWord ++ tailWord_4365193).sum := by decide
  have hdescent : baseEnd_4365193 < baseStart_4365193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365210 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_4365210 : Nat := 118140960795 + 4365210 * 2 ^ 59
def prefixEnd_4365210 : Nat := 4983230072969 + 3 ^ 40 * 4365210 * 2
def baseEnd_4365210 : Nat := 747150295937657109833257

theorem tailTrace_4365210 : CollatzResearch.WordTrace tailWord_4365210 prefixEnd_4365210 747150295937657109833257 := by
  unfold tailWord_4365210
  simp only [CollatzResearch.WordTrace]
  refine ⟨39803072128899290839837271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106141525677064775572899389 39803072128899290839837271)
  ·
    refine ⟨59704608193348936259755907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39803072128899290839837271 59704608193348936259755907)
    ·
      refine ⟨89556912290023404389633861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59704608193348936259755907 89556912290023404389633861)
      ·
        refine ⟨16791921054379388323056349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89556912290023404389633861 16791921054379388323056349)
        ·
          refine ⟨6296970395392270621146131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16791921054379388323056349 6296970395392270621146131)
          ·
            refine ⟨9445455593088405931719197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296970395392270621146131 9445455593088405931719197)
            ·
              refine ⟨3542045847408152224394699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9445455593088405931719197 3542045847408152224394699)
              ·
                refine ⟨5313068771112228336592049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542045847408152224394699 5313068771112228336592049)
                ·
                  refine ⟨3984801578334171252444037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313068771112228336592049 3984801578334171252444037)
                  ·
                    refine ⟨747150295937657109833257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984801578334171252444037 747150295937657109833257)
                    ·
                      rfl

theorem cell23_4365210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_4365210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365210 prefixEnd_4365210 := by exact prefixLift 4365210
  have htrace : WordTrace (prefixWord ++ tailWord_4365210) baseStart_4365210 baseEnd_4365210 := by
    simpa [prefixWord, tailWord_4365210, baseEnd_4365210] using wordTrace_append hprefix tailTrace_4365210
  have hstable : (prefixWord ++ tailWord_4365210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365210).length < 2 ^ (prefixWord ++ tailWord_4365210).sum := by decide
  have hdescent : baseEnd_4365210 < baseStart_4365210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365216 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_4365216 : Nat := 118140960795 + 4365216 * 2 ^ 59
def prefixEnd_4365216 : Nat := 4983230072969 + 3 ^ 40 * 4365216 * 2
def baseEnd_4365216 : Nat := 2241453968696898306024743

theorem tailTrace_4365216 : CollatzResearch.WordTrace tailWord_4365216 prefixEnd_4365216 2241453968696898306024743 := by
  unfold tailWord_4365216
  simp only [CollatzResearch.WordTrace]
  refine ⟨79606253676787713192033751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106141671569050284256045001 79606253676787713192033751)
  ·
    refine ⟨119409380515181569788050627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79606253676787713192033751 119409380515181569788050627)
    ·
      refine ⟨179114070772772354682075941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119409380515181569788050627 179114070772772354682075941)
      ·
        refine ⟨33583888269894816502889239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179114070772772354682075941 33583888269894816502889239)
        ·
          refine ⟨50375832404842224754333859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33583888269894816502889239 50375832404842224754333859)
          ·
            refine ⟨75563748607263337131500789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50375832404842224754333859 75563748607263337131500789)
            ·
              refine ⟨7084101431930937856078199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75563748607263337131500789 7084101431930937856078199)
              ·
                refine ⟨10626152147896406784117299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084101431930937856078199 10626152147896406784117299)
                ·
                  refine ⟨15939228221844610176175949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626152147896406784117299 15939228221844610176175949)
                  ·
                    refine ⟨5977210583191728816065981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15939228221844610176175949 5977210583191728816065981)
                    ·
                      refine ⟨2241453968696898306024743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977210583191728816065981 2241453968696898306024743)
                      ·
                        rfl

theorem cell23_4365216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_4365216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365216 prefixEnd_4365216 := by exact prefixLift 4365216
  have htrace : WordTrace (prefixWord ++ tailWord_4365216) baseStart_4365216 baseEnd_4365216 := by
    simpa [prefixWord, tailWord_4365216, baseEnd_4365216] using wordTrace_append hprefix tailTrace_4365216
  have hstable : (prefixWord ++ tailWord_4365216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365216).length < 2 ^ (prefixWord ++ tailWord_4365216).sum := by decide
  have hdescent : baseEnd_4365216 < baseStart_4365216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365223 : List Nat := [1, 1, 6, 1, 3, 2, 2, 7]
def baseStart_4365223 : Nat := 118140960795 + 4365223 * 2 ^ 59
def prefixEnd_4365223 : Nat := 4983230072969 + 3 ^ 40 * 4365223 * 2
def baseEnd_4365223 : Nat := 83016946780054806616193

theorem tailTrace_4365223 : CollatzResearch.WordTrace tailWord_4365223 prefixEnd_4365223 83016946780054806616193 := by
  unfold tailWord_4365223
  simp only [CollatzResearch.WordTrace]
  refine ⟨159212762664550066579572323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106141841776366711053048215 159212762664550066579572323)
  ·
    refine ⟨238819143996825099869358485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159212762664550066579572323 238819143996825099869358485)
    ·
      refine ⟨11194647374851176556376179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 238819143996825099869358485 11194647374851176556376179)
      ·
        refine ⟨16791971062276764834564269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194647374851176556376179 16791971062276764834564269)
        ·
          refine ⟨6296989148353786812961601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16791971062276764834564269 6296989148353786812961601)
          ·
            refine ⟨4722741861265340109721201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296989148353786812961601 4722741861265340109721201)
            ·
              refine ⟨3542056395949005082290901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722741861265340109721201 3542056395949005082290901)
              ·
                refine ⟨83016946780054806616193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3542056395949005082290901 83016946780054806616193)
                ·
                  rfl

theorem cell23_4365223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 7].length) (baseStart_4365223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365223 prefixEnd_4365223 := by exact prefixLift 4365223
  have htrace : WordTrace (prefixWord ++ tailWord_4365223) baseStart_4365223 baseEnd_4365223 := by
    simpa [prefixWord, tailWord_4365223, baseEnd_4365223] using wordTrace_append hprefix tailTrace_4365223
  have hstable : (prefixWord ++ tailWord_4365223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365223).length < 2 ^ (prefixWord ++ tailWord_4365223).sum := by decide
  have hdescent : baseEnd_4365223 < baseStart_4365223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365261 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4365261 : Nat := 118140960795 + 4365261 * 2 ^ 59
def prefixEnd_4365261 : Nat := 4983230072969 + 3 ^ 40 * 4365261 * 2
def baseEnd_4365261 : Nat := 747159025108783543320679

theorem tailTrace_4365261 : CollatzResearch.WordTrace tailWord_4365261 prefixEnd_4365261 747159025108783543320679 := by
  unfold tailWord_4365261
  simp only [CollatzResearch.WordTrace]
  refine ⟨159214148638412399069455637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106142765758941599379637091 159214148638412399069455637)
  ·
    refine ⟨7463163217425581206380733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159214148638412399069455637 7463163217425581206380733)
    ·
      refine ⟨2798686206534592952392775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7463163217425581206380733 2798686206534592952392775)
      ·
        refine ⟨4198029309801889428589163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798686206534592952392775 4198029309801889428589163)
        ·
          refine ⟨6297043964702834142883745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198029309801889428589163 6297043964702834142883745)
          ·
            refine ⟨4722782973527125607162809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6297043964702834142883745 4722782973527125607162809)
            ·
              refine ⟨3542087230145344205372107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722782973527125607162809 3542087230145344205372107)
              ·
                refine ⟨5313130845218016308058161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542087230145344205372107 5313130845218016308058161)
                ·
                  refine ⟨3984848133913512231043621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313130845218016308058161 3984848133913512231043621)
                  ·
                    refine ⟨747159025108783543320679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984848133913512231043621 747159025108783543320679)
                    ·
                      rfl

theorem cell23_4365261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4365261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365261 prefixEnd_4365261 := by exact prefixLift 4365261
  have htrace : WordTrace (prefixWord ++ tailWord_4365261) baseStart_4365261 baseEnd_4365261 := by
    simpa [prefixWord, tailWord_4365261, baseEnd_4365261] using wordTrace_append hprefix tailTrace_4365261
  have hstable : (prefixWord ++ tailWord_4365261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365261).length < 2 ^ (prefixWord ++ tailWord_4365261).sum := by decide
  have hdescent : baseEnd_4365261 < baseStart_4365261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365277 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_4365277 : Nat := 118140960795 + 4365277 * 2 ^ 59
def prefixEnd_4365277 : Nat := 4983230072969 + 3 ^ 40 * 4365277 * 2
def baseEnd_4365277 : Nat := 2241485291016822567361963

theorem tailTrace_4365277 : CollatzResearch.WordTrace tailWord_4365277 prefixEnd_4365277 2241485291016822567361963 := by
  unfold tailWord_4365277
  simp only [CollatzResearch.WordTrace]
  refine ⟨159214732206354433802038085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106143154804236289201358723 159214732206354433802038085)
  ·
    refine ⟨29852762288691456337882141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159214732206354433802038085 29852762288691456337882141)
    ·
      refine ⟨11194785858259296126705803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29852762288691456337882141 11194785858259296126705803)
      ·
        refine ⟨16792178787388944190058705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194785858259296126705803 16792178787388944190058705)
        ·
          refine ⟨12594134090541708142544029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16792178787388944190058705 12594134090541708142544029)
          ·
            refine ⟨4722800283953140553454011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12594134090541708142544029 4722800283953140553454011)
            ·
              refine ⟨7084200425929710830181017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722800283953140553454011 7084200425929710830181017)
              ·
                refine ⟨5313150319447283122635763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084200425929710830181017 5313150319447283122635763)
                ·
                  refine ⟨7969725479170924683953645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313150319447283122635763 7969725479170924683953645)
                  ·
                    refine ⟨2988647054689096756482617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7969725479170924683953645 2988647054689096756482617)
                    ·
                      refine ⟨2241485291016822567361963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988647054689096756482617 2241485291016822567361963)
                      ·
                        rfl

theorem cell23_4365277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_4365277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365277 prefixEnd_4365277 := by exact prefixLift 4365277
  have htrace : WordTrace (prefixWord ++ tailWord_4365277) baseStart_4365277 baseEnd_4365277 := by
    simpa [prefixWord, tailWord_4365277, baseEnd_4365277] using wordTrace_append hprefix tailTrace_4365277
  have hstable : (prefixWord ++ tailWord_4365277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365277).length < 2 ^ (prefixWord ++ tailWord_4365277).sum := by decide
  have hdescent : baseEnd_4365277 < baseStart_4365277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365296 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 5]
def baseStart_4365296 : Nat := 118140960795 + 4365296 * 2 ^ 59
def prefixEnd_4365296 : Nat := 4983230072969 + 3 ^ 40 * 4365296 * 2
def baseEnd_4365296 : Nat := 249055005238806443669375

theorem tailTrace_4365296 : CollatzResearch.WordTrace tailWord_4365296 prefixEnd_4365296 249055005238806443669375 := by
  unfold tailWord_4365296
  simp only [CollatzResearch.WordTrace]
  refine ⟨79607712596642800023489871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106143616795523733364653161 79607712596642800023489871)
  ·
    refine ⟨119411568894964200035234807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79607712596642800023489871 119411568894964200035234807)
    ·
      refine ⟨179117353342446300052852211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119411568894964200035234807 179117353342446300052852211)
      ·
        refine ⟨268676030013669450079278317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179117353342446300052852211 268676030013669450079278317)
        ·
          refine ⟨100753511255126043779729369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268676030013669450079278317 100753511255126043779729369)
          ·
            refine ⟨75565133441344532834797027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100753511255126043779729369 75565133441344532834797027)
            ·
              refine ⟨113347700162016799252195541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75565133441344532834797027 113347700162016799252195541)
              ·
                refine ⟨2656586722547268732473333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113347700162016799252195541 2656586722547268732473333)
                ·
                  refine ⟨249055005238806443669375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656586722547268732473333 249055005238806443669375)
                  ·
                    rfl

theorem cell23_4365296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 5].length) (baseStart_4365296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365296 prefixEnd_4365296 := by exact prefixLift 4365296
  have htrace : WordTrace (prefixWord ++ tailWord_4365296) baseStart_4365296 baseEnd_4365296 := by
    simpa [prefixWord, tailWord_4365296, baseEnd_4365296] using wordTrace_append hprefix tailTrace_4365296
  have hstable : (prefixWord ++ tailWord_4365296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365296).length < 2 ^ (prefixWord ++ tailWord_4365296).sum := by decide
  have hdescent : baseEnd_4365296 < baseStart_4365296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365309 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_4365309 : Nat := 118140960795 + 4365309 * 2 ^ 59
def prefixEnd_4365309 : Nat := 4983230072969 + 3 ^ 40 * 4365309 * 2
def baseEnd_4365309 : Nat := 747167240799255480720605

theorem tailTrace_4365309 : CollatzResearch.WordTrace tailWord_4365309 prefixEnd_4365309 747167240799255480720605 := by
  unfold tailWord_4365309
  simp only [CollatzResearch.WordTrace]
  refine ⟨159215899342238503267202981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106143932894825668844801987 159215899342238503267202981)
  ·
    refine ⟨29852981126669719362600559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159215899342238503267202981 29852981126669719362600559)
    ·
      refine ⟨44779471690004579043900839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29852981126669719362600559 44779471690004579043900839)
      ·
        refine ⟨67169207535006868565851259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44779471690004579043900839 67169207535006868565851259)
        ·
          refine ⟨100753811302510302848776889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67169207535006868565851259 100753811302510302848776889)
          ·
            refine ⟨75565358476882727136582667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100753811302510302848776889 75565358476882727136582667)
            ·
              refine ⟨113348037715324090704874001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75565358476882727136582667 113348037715324090704874001)
              ·
                refine ⟨85011028286493068028655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113348037715324090704874001 85011028286493068028655501)
                ·
                  refine ⟨31879135607434900510745813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85011028286493068028655501 31879135607434900510745813)
                  ·
                    refine ⟨747167240799255480720605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31879135607434900510745813 747167240799255480720605)
                    ·
                      rfl

theorem cell23_4365309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_4365309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365309 prefixEnd_4365309 := by exact prefixLift 4365309
  have htrace : WordTrace (prefixWord ++ tailWord_4365309) baseStart_4365309 baseEnd_4365309 := by
    simpa [prefixWord, tailWord_4365309, baseEnd_4365309] using wordTrace_append hprefix tailTrace_4365309
  have hstable : (prefixWord ++ tailWord_4365309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365309).length < 2 ^ (prefixWord ++ tailWord_4365309).sum := by decide
  have hdescent : baseEnd_4365309 < baseStart_4365309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365313 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 5]
def baseStart_4365313 : Nat := 118140960795 + 4365313 * 2 ^ 59
def prefixEnd_4365313 : Nat := 4983230072969 + 3 ^ 40 * 4365313 * 2
def baseEnd_4365313 : Nat := 249055975146709380723533

theorem tailTrace_4365313 : CollatzResearch.WordTrace tailWord_4365313 prefixEnd_4365313 249055975146709380723533 := by
  unfold tailWord_4365313
  simp only [CollatzResearch.WordTrace]
  refine ⟨159216045234224011950348593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106144030156149341300232395 159216045234224011950348593)
  ·
    refine ⟨119412033925668008962761445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159216045234224011950348593 119412033925668008962761445)
    ·
      refine ⟨22389756361062751680517771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119412033925668008962761445 22389756361062751680517771)
      ·
        refine ⟨33584634541594127520776657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22389756361062751680517771 33584634541594127520776657)
        ·
          refine ⟨25188475906195595640582493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33584634541594127520776657 25188475906195595640582493)
          ·
            refine ⟨9445678464823348365218435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25188475906195595640582493 9445678464823348365218435)
            ·
              refine ⟨14168517697235022547827653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9445678464823348365218435 14168517697235022547827653)
              ·
                refine ⟨2656597068231566727717685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14168517697235022547827653 2656597068231566727717685)
                ·
                  refine ⟨249055975146709380723533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656597068231566727717685 249055975146709380723533)
                  ·
                    rfl

theorem cell23_4365313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 5].length) (baseStart_4365313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365313 prefixEnd_4365313 := by exact prefixLift 4365313
  have htrace : WordTrace (prefixWord ++ tailWord_4365313) baseStart_4365313 baseEnd_4365313 := by
    simpa [prefixWord, tailWord_4365313, baseEnd_4365313] using wordTrace_append hprefix tailTrace_4365313
  have hstable : (prefixWord ++ tailWord_4365313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365313).length < 2 ^ (prefixWord ++ tailWord_4365313).sum := by decide
  have hdescent : baseEnd_4365313 < baseStart_4365313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365343 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 2, 5]
def baseStart_4365343 : Nat := 118140960795 + 4365343 * 2 ^ 59
def prefixEnd_4365343 : Nat := 4983230072969 + 3 ^ 40 * 4365343 * 2
def baseEnd_4365343 : Nat := 747173060246673103045553

theorem tailTrace_4365343 : CollatzResearch.WordTrace tailWord_4365343 prefixEnd_4365343 747173060246673103045553 := by
  unfold tailWord_4365343
  simp only [CollatzResearch.WordTrace]
  refine ⟨159217139424115327073940683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106144759616076884715960455 159217139424115327073940683)
  ·
    refine ⟨238825709136172990610911025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159217139424115327073940683 238825709136172990610911025)
    ·
      refine ⟨179119281852129742958183269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238825709136172990610911025 179119281852129742958183269)
      ·
        refine ⟨33584865347274326804659363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179119281852129742958183269 33584865347274326804659363)
        ·
          refine ⟨50377298020911490206989045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33584865347274326804659363 50377298020911490206989045)
          ·
            refine ⟨4722871689460452206905223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50377298020911490206989045 4722871689460452206905223)
            ·
              refine ⟨7084307534190678310357835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722871689460452206905223 7084307534190678310357835)
              ·
                refine ⟨10626461301286017465536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084307534190678310357835 10626461301286017465536753)
                ·
                  refine ⟨7969845975964513099152565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10626461301286017465536753 7969845975964513099152565)
                  ·
                    refine ⟨747173060246673103045553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7969845975964513099152565 747173060246673103045553)
                    ·
                      rfl

theorem cell23_4365343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_4365343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365343 prefixEnd_4365343 := by exact prefixLift 4365343
  have htrace : WordTrace (prefixWord ++ tailWord_4365343) baseStart_4365343 baseEnd_4365343 := by
    simpa [prefixWord, tailWord_4365343, baseEnd_4365343] using wordTrace_append hprefix tailTrace_4365343
  have hstable : (prefixWord ++ tailWord_4365343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365343).length < 2 ^ (prefixWord ++ tailWord_4365343).sum := by decide
  have hdescent : baseEnd_4365343 < baseStart_4365343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365356 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_4365356 : Nat := 118140960795 + 4365356 * 2 ^ 59
def prefixEnd_4365356 : Nat := 4983230072969 + 3 ^ 40 * 4365356 * 2
def baseEnd_4365356 : Nat := 747175285329509252758033

theorem tailTrace_4365356 : CollatzResearch.WordTrace tailWord_4365356 prefixEnd_4365356 747175285329509252758033 := by
  unfold tailWord_4365356
  simp only [CollatzResearch.WordTrace]
  refine ⟨79608806786534115147081961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106145075715378820196109281 79608806786534115147081961)
  ·
    refine ⟨59706605089900586360311471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79608806786534115147081961 59706605089900586360311471)
    ·
      refine ⟨89559907634850879540467207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59706605089900586360311471 89559907634850879540467207)
      ·
        refine ⟨134339861452276319310700811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89559907634850879540467207 134339861452276319310700811)
        ·
          refine ⟨201509792178414478966051217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134339861452276319310700811 201509792178414478966051217)
          ·
            refine ⟨151132344133810859224538413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201509792178414478966051217 151132344133810859224538413)
            ·
              refine ⟨56674629050179072209201905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151132344133810859224538413 56674629050179072209201905)
              ·
                refine ⟨42505971787634304156901429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56674629050179072209201905 42505971787634304156901429)
                ·
                  refine ⟨3984934855090716014709509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42505971787634304156901429 3984934855090716014709509)
                  ·
                    refine ⟨747175285329509252758033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984934855090716014709509 747175285329509252758033)
                    ·
                      rfl

theorem cell23_4365356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_4365356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365356 prefixEnd_4365356 := by exact prefixLift 4365356
  have htrace : WordTrace (prefixWord ++ tailWord_4365356) baseStart_4365356 baseEnd_4365356 := by
    simpa [prefixWord, tailWord_4365356, baseEnd_4365356] using wordTrace_append hprefix tailTrace_4365356
  have hstable : (prefixWord ++ tailWord_4365356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365356).length < 2 ^ (prefixWord ++ tailWord_4365356).sum := by decide
  have hdescent : baseEnd_4365356 < baseStart_4365356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365373 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_4365373 : Nat := 118140960795 + 4365373 * 2 ^ 59
def prefixEnd_4365373 : Nat := 4983230072969 + 3 ^ 40 * 4365373 * 2
def baseEnd_4365373 : Nat := 747178195053218063920507

theorem tailTrace_4365373 : CollatzResearch.WordTrace tailWord_4365373 prefixEnd_4365373 747178195053218063920507 := by
  unfold tailWord_4365373
  simp only [CollatzResearch.WordTrace]
  refine ⟨159218233614006642197532773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106145489076004428131688515 159218233614006642197532773)
  ·
    refine ⟨29853418802626245412037395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159218233614006642197532773 29853418802626245412037395)
    ·
      refine ⟨44780128203939368118056093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29853418802626245412037395 44780128203939368118056093)
      ·
        refine ⟨16792548076477263044271035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44780128203939368118056093 16792548076477263044271035)
        ·
          refine ⟨25188822114715894566406553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16792548076477263044271035 25188822114715894566406553)
          ·
            refine ⟨18891616586036920924804915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25188822114715894566406553 18891616586036920924804915)
            ·
              refine ⟨28337424879055381387207373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18891616586036920924804915 28337424879055381387207373)
              ·
                refine ⟨10626534329645768020202765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28337424879055381387207373 10626534329645768020202765)
                ·
                  refine ⟨3984950373617163007576037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10626534329645768020202765 3984950373617163007576037)
                  ·
                    refine ⟨747178195053218063920507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984950373617163007576037 747178195053218063920507)
                    ·
                      rfl

theorem cell23_4365373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_4365373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365373 prefixEnd_4365373 := by exact prefixLift 4365373
  have htrace : WordTrace (prefixWord ++ tailWord_4365373) baseStart_4365373 baseEnd_4365373 := by
    simpa [prefixWord, tailWord_4365373, baseEnd_4365373] using wordTrace_append hprefix tailTrace_4365373
  have hstable : (prefixWord ++ tailWord_4365373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365373).length < 2 ^ (prefixWord ++ tailWord_4365373).sum := by decide
  have hdescent : baseEnd_4365373 < baseStart_4365373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365386 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_4365386 : Nat := 118140960795 + 4365386 * 2 ^ 59
def prefixEnd_4365386 : Nat := 4983230072969 + 3 ^ 40 * 4365386 * 2
def baseEnd_4365386 : Nat := 249060140045351404544329

theorem tailTrace_4365386 : CollatzResearch.WordTrace tailWord_4365386 prefixEnd_4365386 249060140045351404544329 := by
  unfold tailWord_4365386
  simp only [CollatzResearch.WordTrace]
  refine ⟨39804676940739886354439003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106145805175306363611837341 39804676940739886354439003)
  ·
    refine ⟨59707015411109829531658505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39804676940739886354439003 59707015411109829531658505)
    ·
      refine ⟨44780261558332372148743879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59707015411109829531658505 44780261558332372148743879)
      ·
        refine ⟨67170392337498558223115819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44780261558332372148743879 67170392337498558223115819)
        ·
          refine ⟨100755588506247837334673729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67170392337498558223115819 100755588506247837334673729)
          ·
            refine ⟨75566691379685878001005297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100755588506247837334673729 75566691379685878001005297)
            ·
              refine ⟨56675018534764408500753973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75566691379685878001005297 56675018534764408500753973)
              ·
                refine ⟨5313282987634163296945685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56675018534764408500753973 5313282987634163296945685)
                ·
                  refine ⟨249060140045351404544329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5313282987634163296945685 249060140045351404544329)
                  ·
                    rfl

theorem cell23_4365386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_4365386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365386 prefixEnd_4365386 := by exact prefixLift 4365386
  have htrace : WordTrace (prefixWord ++ tailWord_4365386) baseStart_4365386 baseEnd_4365386 := by
    simpa [prefixWord, tailWord_4365386, baseEnd_4365386] using wordTrace_append hprefix tailTrace_4365386
  have hstable : (prefixWord ++ tailWord_4365386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365386).length < 2 ^ (prefixWord ++ tailWord_4365386).sum := by decide
  have hdescent : baseEnd_4365386 < baseStart_4365386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365463 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 1, 6]
def baseStart_4365463 : Nat := 118140960795 + 4365463 * 2 ^ 59
def prefixEnd_4365463 : Nat := 4983230072969 + 3 ^ 40 * 4365463 * 2
def baseEnd_4365463 : Nat := 747193599472852946545369

theorem tailTrace_4365463 : CollatzResearch.WordTrace tailWord_4365463 prefixEnd_4365463 747193599472852946545369 := by
  unfold tailWord_4365463
  simp only [CollatzResearch.WordTrace]
  refine ⟨159221516183680587568309043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106147677455787058378872695 159221516183680587568309043)
  ·
    refine ⟨238832274275520881352463565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159221516183680587568309043 238832274275520881352463565)
    ·
      refine ⟨89562102853320330507173837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238832274275520881352463565 89562102853320330507173837)
      ·
        refine ⟨33585788569995123940190189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89562102853320330507173837 33585788569995123940190189)
        ·
          refine ⟨12594670713748171477571321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33585788569995123940190189 12594670713748171477571321)
          ·
            refine ⟨9446003035311128608178491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12594670713748171477571321 9446003035311128608178491)
            ·
              refine ⟨14169004552966692912267737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446003035311128608178491 14169004552966692912267737)
              ·
                refine ⟨10626753414725019684200803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14169004552966692912267737 10626753414725019684200803)
                ·
                  refine ⟨15940130122087529526301205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626753414725019684200803 15940130122087529526301205)
                  ·
                    refine ⟨747193599472852946545369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15940130122087529526301205 747193599472852946545369)
                    ·
                      rfl

theorem cell23_4365463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_4365463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365463 prefixEnd_4365463 := by exact prefixLift 4365463
  have htrace : WordTrace (prefixWord ++ tailWord_4365463) baseStart_4365463 baseEnd_4365463 := by
    simpa [prefixWord, tailWord_4365463, baseEnd_4365463] using wordTrace_append hprefix tailTrace_4365463
  have hstable : (prefixWord ++ tailWord_4365463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365463).length < 2 ^ (prefixWord ++ tailWord_4365463).sum := by decide
  have hdescent : baseEnd_4365463 < baseStart_4365463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365476 : List Nat := [2, 3, 1, 2, 3, 12]
def baseStart_4365476 : Nat := 118140960795 + 4365476 * 2 ^ 59
def prefixEnd_4365476 : Nat := 4983230072969 + 3 ^ 40 * 4365476 * 2
def baseEnd_4365476 : Nat := 9224639809329495015529

theorem tailTrace_4365476 : CollatzResearch.WordTrace tailWord_4365476 prefixEnd_4365476 9224639809329495015529 := by
  unfold tailWord_4365476
  simp only [CollatzResearch.WordTrace]
  refine ⟨79610995166316745394266141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106147993555088993859021521 79610995166316745394266141)
  ·
    refine ⟨29854123187368779522849803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79610995166316745394266141 29854123187368779522849803)
    ·
      refine ⟨44781184781053169284274705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29854123187368779522849803 44781184781053169284274705)
      ·
        refine ⟨33585888585789876963206029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44781184781053169284274705 33585888585789876963206029)
        ·
          refine ⟨12594708219671203861202261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33585888585789876963206029 12594708219671203861202261)
          ·
            refine ⟨9224639809329495015529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12594708219671203861202261 9224639809329495015529)
            ·
              rfl

theorem cell23_4365476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 12].length) (baseStart_4365476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365476 prefixEnd_4365476 := by exact prefixLift 4365476
  have htrace : WordTrace (prefixWord ++ tailWord_4365476) baseStart_4365476 baseEnd_4365476 := by
    simpa [prefixWord, tailWord_4365476, baseEnd_4365476] using wordTrace_append hprefix tailTrace_4365476
  have hstable : (prefixWord ++ tailWord_4365476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365476).length < 2 ^ (prefixWord ++ tailWord_4365476).sum := by decide
  have hdescent : baseEnd_4365476 < baseStart_4365476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365500 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_4365500 : Nat := 118140960795 + 4365500 * 2 ^ 59
def prefixEnd_4365500 : Nat := 4983230072969 + 3 ^ 40 * 4365500 * 2
def baseEnd_4365500 : Nat := 2241599797202775194873437

theorem tailTrace_4365500 : CollatzResearch.WordTrace tailWord_4365500 prefixEnd_4365500 2241599797202775194873437 := by
  unfold tailWord_4365500
  simp only [CollatzResearch.WordTrace]
  refine ⟨79611432842273271443702977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106148577123031028591603969 79611432842273271443702977)
  ·
    refine ⟨59708574631704953582777233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79611432842273271443702977 59708574631704953582777233)
    ·
      refine ⟨44781430973778715187082925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59708574631704953582777233 44781430973778715187082925)
      ·
        refine ⟨16793036615167018195156097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44781430973778715187082925 16793036615167018195156097)
        ·
          refine ⟨12594777461375263646367073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16793036615167018195156097 12594777461375263646367073)
          ·
            refine ⟨9446083096031447734775305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12594777461375263646367073 9446083096031447734775305)
            ·
              refine ⟨7084562322023585801081479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9446083096031447734775305 7084562322023585801081479)
              ·
                refine ⟨10626843483035378701622219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084562322023585801081479 10626843483035378701622219)
                ·
                  refine ⟨15940265224553068052433329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626843483035378701622219 15940265224553068052433329)
                  ·
                    refine ⟨11955198918414801039324997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15940265224553068052433329 11955198918414801039324997)
                    ·
                      refine ⟨2241599797202775194873437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11955198918414801039324997 2241599797202775194873437)
                      ·
                        rfl

theorem cell23_4365500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_4365500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365500 prefixEnd_4365500 := by exact prefixLift 4365500
  have htrace : WordTrace (prefixWord ++ tailWord_4365500) baseStart_4365500 baseEnd_4365500 := by
    simpa [prefixWord, tailWord_4365500, baseEnd_4365500] using wordTrace_append hprefix tailTrace_4365500
  have hstable : (prefixWord ++ tailWord_4365500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365500).length < 2 ^ (prefixWord ++ tailWord_4365500).sum := by decide
  have hdescent : baseEnd_4365500 < baseStart_4365500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365503 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_4365503 : Nat := 118140960795 + 4365503 * 2 ^ 59
def prefixEnd_4365503 : Nat := 4983230072969 + 3 ^ 40 * 4365503 * 2
def baseEnd_4365503 : Nat := 2241601337644738683135923

theorem tailTrace_4365503 : CollatzResearch.WordTrace tailWord_4365503 prefixEnd_4365503 2241601337644738683135923 := by
  unfold tailWord_4365503
  simp only [CollatzResearch.WordTrace]
  refine ⟨159222975103535674399765163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106148650069023782933176775 159222975103535674399765163)
  ·
    refine ⟨238834462655303511599647745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159222975103535674399765163 238834462655303511599647745)
    ·
      refine ⟨179125846991477633699735809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238834462655303511599647745 179125846991477633699735809)
      ·
        refine ⟨134344385243608225274801857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179125846991477633699735809 134344385243608225274801857)
        ·
          refine ⟨100758288932706168956101393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134344385243608225274801857 100758288932706168956101393)
          ·
            refine ⟨75568716699529626717076045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100758288932706168956101393 75568716699529626717076045)
            ·
              refine ⟨28338268762323610018903517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75568716699529626717076045 28338268762323610018903517)
              ·
                refine ⟨10626850785871353757088819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28338268762323610018903517 10626850785871353757088819)
                ·
                  refine ⟨15940276178807030635633229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626850785871353757088819 15940276178807030635633229)
                  ·
                    refine ⟨5977603567052636488362461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15940276178807030635633229 5977603567052636488362461)
                    ·
                      refine ⟨2241601337644738683135923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977603567052636488362461 2241601337644738683135923)
                      ·
                        rfl

theorem cell23_4365503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_4365503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365503 prefixEnd_4365503 := by exact prefixLift 4365503
  have htrace : WordTrace (prefixWord ++ tailWord_4365503) baseStart_4365503 baseEnd_4365503 := by
    simpa [prefixWord, tailWord_4365503, baseEnd_4365503] using wordTrace_append hprefix tailTrace_4365503
  have hstable : (prefixWord ++ tailWord_4365503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365503).length < 2 ^ (prefixWord ++ tailWord_4365503).sum := by decide
  have hdescent : baseEnd_4365503 < baseStart_4365503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365524 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4365524 : Nat := 118140960795 + 4365524 * 2 ^ 59
def prefixEnd_4365524 : Nat := 4983230072969 + 3 ^ 40 * 4365524 * 2
def baseEnd_4365524 : Nat := 2241612120738483100973327

theorem tailTrace_4365524 : CollatzResearch.WordTrace tailWord_4365524 prefixEnd_4365524 2241612120738483100973327 := by
  unfold tailWord_4365524
  simp only [CollatzResearch.WordTrace]
  refine ⟨79611870518229797493139813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106149160690973063324186417 79611870518229797493139813)
  ·
    refine ⟨14927225722168087029963715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79611870518229797493139813 14927225722168087029963715)
    ·
      refine ⟨22390838583252130544945573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14927225722168087029963715 22390838583252130544945573)
      ·
        refine ⟨4198282234359774477177295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22390838583252130544945573 4198282234359774477177295)
        ·
          refine ⟨6297423351539661715765943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198282234359774477177295 6297423351539661715765943)
          ·
            refine ⟨9446135027309492573648915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297423351539661715765943 9446135027309492573648915)
            ·
              refine ⟨14169202540964238860473373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446135027309492573648915 14169202540964238860473373)
              ·
                refine ⟨5313450952861589572677515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14169202540964238860473373 5313450952861589572677515)
                ·
                  refine ⟨7970176429292384359016273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313450952861589572677515 7970176429292384359016273)
                  ·
                    refine ⟨5977632321969288269262205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7970176429292384359016273 5977632321969288269262205)
                    ·
                      refine ⟨2241612120738483100973327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977632321969288269262205 2241612120738483100973327)
                      ·
                        rfl

theorem cell23_4365524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4365524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365524 prefixEnd_4365524 := by exact prefixLift 4365524
  have htrace : WordTrace (prefixWord ++ tailWord_4365524) baseStart_4365524 baseEnd_4365524 := by
    simpa [prefixWord, tailWord_4365524, baseEnd_4365524] using wordTrace_append hprefix tailTrace_4365524
  have hstable : (prefixWord ++ tailWord_4365524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365524).length < 2 ^ (prefixWord ++ tailWord_4365524).sum := by decide
  have hdescent : baseEnd_4365524 < baseStart_4365524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365537 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_4365537 : Nat := 118140960795 + 4365537 * 2 ^ 59
def prefixEnd_4365537 : Nat := 4983230072969 + 3 ^ 40 * 4365537 * 2
def baseEnd_4365537 : Nat := 2241618795986991550110767

theorem tailTrace_4365537 : CollatzResearch.WordTrace tailWord_4365537 prefixEnd_4365537 2241618795986991550110767 := by
  unfold tailWord_4365537
  simp only [CollatzResearch.WordTrace]
  refine ⟨159224215185412498206502865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106149476790274998804335243 159224215185412498206502865)
  ·
    refine ⟨119418161389059373654877149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159224215185412498206502865 119418161389059373654877149)
    ·
      refine ⟨44781810520897265120578931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119418161389059373654877149 44781810520897265120578931)
      ·
        refine ⟨67172715781345897680868397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44781810520897265120578931 67172715781345897680868397)
        ·
          refine ⟨25189768418004711630325649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67172715781345897680868397 25189768418004711630325649)
          ·
            refine ⟨18892326313503533722744237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25189768418004711630325649 18892326313503533722744237)
            ·
              refine ⟨7084622367563825146029089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18892326313503533722744237 7084622367563825146029089)
              ·
                refine ⟨5313466775672868859521817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084622367563825146029089 5313466775672868859521817)
                ·
                  refine ⟨3985100081754651644641363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313466775672868859521817 3985100081754651644641363)
                  ·
                    refine ⟨5977650122631977466962045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985100081754651644641363 5977650122631977466962045)
                    ·
                      refine ⟨2241618795986991550110767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977650122631977466962045 2241618795986991550110767)
                      ·
                        rfl

theorem cell23_4365537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_4365537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365537 prefixEnd_4365537 := by exact prefixLift 4365537
  have htrace : WordTrace (prefixWord ++ tailWord_4365537) baseStart_4365537 baseEnd_4365537 := by
    simpa [prefixWord, tailWord_4365537, baseEnd_4365537] using wordTrace_append hprefix tailTrace_4365537
  have hstable : (prefixWord ++ tailWord_4365537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365537).length < 2 ^ (prefixWord ++ tailWord_4365537).sum := by decide
  have hdescent : baseEnd_4365537 < baseStart_4365537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365554 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4365554 : Nat := 118140960795 + 4365554 * 2 ^ 59
def prefixEnd_4365554 : Nat := 4983230072969 + 3 ^ 40 * 4365554 * 2
def baseEnd_4365554 : Nat := 2241627525158117983598189

theorem tailTrace_4365554 : CollatzResearch.WordTrace tailWord_4365554 prefixEnd_4365554 2241627525158117983598189 := by
  unfold tailWord_4365554
  simp only [CollatzResearch.WordTrace]
  refine ⟨39806208806587727527467929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106149890150900606739914477 39806208806587727527467929)
  ·
    refine ⟨29854656604940795645600947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39806208806587727527467929 29854656604940795645600947)
    ·
      refine ⟨44781984907411193468401421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29854656604940795645600947 44781984907411193468401421)
      ·
        refine ⟨16793244340279197550650533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44781984907411193468401421 16793244340279197550650533)
        ·
          refine ⟨3148733313802349540746975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16793244340279197550650533 3148733313802349540746975)
          ·
            refine ⟨4723099970703524311120463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148733313802349540746975 4723099970703524311120463)
            ·
              refine ⟨7084649956055286466680695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723099970703524311120463 7084649956055286466680695)
              ·
                refine ⟨10626974934082929700021043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084649956055286466680695 10626974934082929700021043)
                ·
                  refine ⟨15940462401124394550031565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10626974934082929700021043 15940462401124394550031565)
                  ·
                    refine ⟨5977673400421647956261837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15940462401124394550031565 5977673400421647956261837)
                    ·
                      refine ⟨2241627525158117983598189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977673400421647956261837 2241627525158117983598189)
                      ·
                        rfl

theorem cell23_4365554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4365554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365554 prefixEnd_4365554 := by exact prefixLift 4365554
  have htrace : WordTrace (prefixWord ++ tailWord_4365554) baseStart_4365554 baseEnd_4365554 := by
    simpa [prefixWord, tailWord_4365554, baseEnd_4365554] using wordTrace_append hprefix tailTrace_4365554
  have hstable : (prefixWord ++ tailWord_4365554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365554).length < 2 ^ (prefixWord ++ tailWord_4365554).sum := by decide
  have hdescent : baseEnd_4365554 < baseStart_4365554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365564 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_4365564 : Nat := 118140960795 + 4365564 * 2 ^ 59
def prefixEnd_4365564 : Nat := 4983230072969 + 3 ^ 40 * 4365564 * 2
def baseEnd_4365564 : Nat := 2241632659964662944473143

theorem tailTrace_4365564 : CollatzResearch.WordTrace tailWord_4365564 prefixEnd_4365564 2241632659964662944473143 := by
  unfold tailWord_4365564
  simp only [CollatzResearch.WordTrace]
  refine ⟨79612599978157340908867873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106150133304209787878490497 79612599978157340908867873)
  ·
    refine ⟨59709449983618005681650905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79612599978157340908867873 59709449983618005681650905)
    ·
      refine ⟨44782087487713504261238179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59709449983618005681650905 44782087487713504261238179)
      ·
        refine ⟨67173131231570256391857269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44782087487713504261238179 67173131231570256391857269)
        ·
          refine ⟨6297481052959711536736619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67173131231570256391857269 6297481052959711536736619)
          ·
            refine ⟨9446221579439567305104929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297481052959711536736619 9446221579439567305104929)
            ·
              refine ⟨7084666184579675478828697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9446221579439567305104929 7084666184579675478828697)
              ·
                refine ⟨5313499638434756609121523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084666184579675478828697 5313499638434756609121523)
                ·
                  refine ⟨7970249457652134913682285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313499638434756609121523 7970249457652134913682285)
                  ·
                    refine ⟨2988843546619550592630857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7970249457652134913682285 2988843546619550592630857)
                    ·
                      refine ⟨2241632659964662944473143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988843546619550592630857 2241632659964662944473143)
                      ·
                        rfl

theorem cell23_4365564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_4365564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365564 prefixEnd_4365564 := by exact prefixLift 4365564
  have htrace : WordTrace (prefixWord ++ tailWord_4365564) baseStart_4365564 baseEnd_4365564 := by
    simpa [prefixWord, tailWord_4365564, baseEnd_4365564] using wordTrace_append hprefix tailTrace_4365564
  have hstable : (prefixWord ++ tailWord_4365564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365564).length < 2 ^ (prefixWord ++ tailWord_4365564).sum := by decide
  have hdescent : baseEnd_4365564 < baseStart_4365564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365661 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4365661 : Nat := 118140960795 + 4365661 * 2 ^ 59
def prefixEnd_4365661 : Nat := 4983230072969 + 3 ^ 40 * 4365661 * 2
def baseEnd_4365661 : Nat := 2241682467588149064960197

theorem tailTrace_4365661 : CollatzResearch.WordTrace tailWord_4365661 prefixEnd_4365661 2241682467588149064960197 := by
  unfold tailWord_4365661
  simp only [CollatzResearch.WordTrace]
  refine ⟨159228737836963267384016837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106152491891308844922677891 159228737836963267384016837)
  ·
    refine ⟨29855388344430612634503157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159228737836963267384016837 29855388344430612634503157)
    ·
      refine ⟨2798942657290369934484671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29855388344430612634503157 2798942657290369934484671)
      ·
        refine ⟨4198413985935554901727007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798942657290369934484671 4198413985935554901727007)
        ·
          refine ⟨6297620978903332352590511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198413985935554901727007 6297620978903332352590511)
          ·
            refine ⟨9446431468354998528885767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297620978903332352590511 9446431468354998528885767)
            ·
              refine ⟨14169647202532497793328651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446431468354998528885767 14169647202532497793328651)
              ·
                refine ⟨21254470803798746689992977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14169647202532497793328651 21254470803798746689992977)
                ·
                  refine ⟨15940853102849060017494733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21254470803798746689992977 15940853102849060017494733)
                  ·
                    refine ⟨5977819913568397506560525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15940853102849060017494733 5977819913568397506560525)
                    ·
                      refine ⟨2241682467588149064960197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977819913568397506560525 2241682467588149064960197)
                      ·
                        rfl

theorem cell23_4365661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4365661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365661 prefixEnd_4365661 := by exact prefixLift 4365661
  have htrace : WordTrace (prefixWord ++ tailWord_4365661) baseStart_4365661 baseEnd_4365661 := by
    simpa [prefixWord, tailWord_4365661, baseEnd_4365661] using wordTrace_append hprefix tailTrace_4365661
  have hstable : (prefixWord ++ tailWord_4365661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365661).length < 2 ^ (prefixWord ++ tailWord_4365661).sum := by decide
  have hdescent : baseEnd_4365661 < baseStart_4365661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365663 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_4365663 : Nat := 118140960795 + 4365663 * 2 ^ 59
def prefixEnd_4365663 : Nat := 4983230072969 + 3 ^ 40 * 4365663 * 2
def baseEnd_4365663 : Nat := 2241683494549458057135187

theorem tailTrace_4365663 : CollatzResearch.WordTrace tailWord_4365663 prefixEnd_4365663 2241683494549458057135187 := by
  unfold tailWord_4365663
  simp only [CollatzResearch.WordTrace]
  refine ⟨159228810782956021725589643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106152540521970681150393095 159228810782956021725589643)
  ·
    refine ⟨238843216174434032588384465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159228810782956021725589643 238843216174434032588384465)
    ·
      refine ⟨179132412130825524441288349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238843216174434032588384465 179132412130825524441288349)
      ·
        refine ⟨67174654549059571665483131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179132412130825524441288349 67174654549059571665483131)
        ·
          refine ⟨100761981823589357498224697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67174654549059571665483131 100761981823589357498224697)
          ·
            refine ⟨75571486367692018123668523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100761981823589357498224697 75571486367692018123668523)
            ·
              refine ⟨113357229551538027185502785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75571486367692018123668523 113357229551538027185502785)
              ·
                refine ⟨85017922163653520389127089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113357229551538027185502785 85017922163653520389127089)
                ·
                  refine ⟨63763441622740140291845317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85017922163653520389127089 63763441622740140291845317)
                  ·
                    refine ⟨11955645304263776304720997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63763441622740140291845317 11955645304263776304720997)
                    ·
                      refine ⟨2241683494549458057135187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11955645304263776304720997 2241683494549458057135187)
                      ·
                        rfl

theorem cell23_4365663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_4365663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365663 prefixEnd_4365663 := by exact prefixLift 4365663
  have htrace : WordTrace (prefixWord ++ tailWord_4365663) baseStart_4365663 baseEnd_4365663 := by
    simpa [prefixWord, tailWord_4365663, baseEnd_4365663] using wordTrace_append hprefix tailTrace_4365663
  have hstable : (prefixWord ++ tailWord_4365663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365663).length < 2 ^ (prefixWord ++ tailWord_4365663).sum := by decide
  have hdescent : baseEnd_4365663 < baseStart_4365663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365667 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 2, 4, 2]
def baseStart_4365667 : Nat := 118140960795 + 4365667 * 2 ^ 59
def prefixEnd_4365667 : Nat := 4983230072969 + 3 ^ 40 * 4365667 * 2
def baseEnd_4365667 : Nat := 2241685548472076041485169

theorem tailTrace_4365667 : CollatzResearch.WordTrace tailWord_4365667 prefixEnd_4365667 2241685548472076041485169 := by
  unfold tailWord_4365667
  simp only [CollatzResearch.WordTrace]
  refine ⟨159228956674941530408735255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106152637783294353605823503 159228956674941530408735255)
  ·
    refine ⟨238843435012412295613102883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159228956674941530408735255 238843435012412295613102883)
    ·
      refine ⟨358265152518618443419654325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238843435012412295613102883 358265152518618443419654325)
      ·
        refine ⟨33587358048620479070592593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 358265152518618443419654325 33587358048620479070592593)
        ·
          refine ⟨25190518536465359302944445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33587358048620479070592593 25190518536465359302944445)
          ·
            refine ⟨9446444451174509738604167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25190518536465359302944445 9446444451174509738604167)
            ·
              refine ⟨14169666676761764607906251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446444451174509738604167 14169666676761764607906251)
              ·
                refine ⟨21254500015142646911859377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14169666676761764607906251 21254500015142646911859377)
                ·
                  refine ⟨15940875011356985183894533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21254500015142646911859377 15940875011356985183894533)
                  ·
                    refine ⟨2988914064629434721980225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15940875011356985183894533 2988914064629434721980225)
                    ·
                      refine ⟨2241685548472076041485169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988914064629434721980225 2241685548472076041485169)
                      ·
                        rfl

theorem cell23_4365667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_4365667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365667 prefixEnd_4365667 := by exact prefixLift 4365667
  have htrace : WordTrace (prefixWord ++ tailWord_4365667) baseStart_4365667 baseEnd_4365667 := by
    simpa [prefixWord, tailWord_4365667, baseEnd_4365667] using wordTrace_append hprefix tailTrace_4365667
  have hstable : (prefixWord ++ tailWord_4365667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365667).length < 2 ^ (prefixWord ++ tailWord_4365667).sum := by decide
  have hdescent : baseEnd_4365667 < baseStart_4365667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365677 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_4365677 : Nat := 118140960795 + 4365677 * 2 ^ 59
def prefixEnd_4365677 : Nat := 4983230072969 + 3 ^ 40 * 4365677 * 2
def baseEnd_4365677 : Nat := 747230227759540334120041

theorem tailTrace_4365677 : CollatzResearch.WordTrace tailWord_4365677 prefixEnd_4365677 747230227759540334120041 := by
  unfold tailWord_4365677
  simp only [CollatzResearch.WordTrace]
  refine ⟨159229321404905302116599285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106152880936603534744399523 159229321404905302116599285)
  ·
    refine ⟨14927748881709872073431183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159229321404905302116599285 14927748881709872073431183)
    ·
      refine ⟨22391623322564808110146775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14927748881709872073431183 22391623322564808110146775)
      ·
        refine ⟨33587434983847212165220163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22391623322564808110146775 33587434983847212165220163)
        ·
          refine ⟨50381152475770818247830245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33587434983847212165220163 50381152475770818247830245)
          ·
            refine ⟨9446466089207028421468171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50381152475770818247830245 9446466089207028421468171)
            ·
              refine ⟨14169699133810542632202257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446466089207028421468171 14169699133810542632202257)
              ·
                refine ⟨10627274350357906974151693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14169699133810542632202257 10627274350357906974151693)
                ·
                  refine ⟨3985227881384215115306885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10627274350357906974151693 3985227881384215115306885)
                  ·
                    refine ⟨747230227759540334120041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985227881384215115306885 747230227759540334120041)
                    ·
                      rfl

theorem cell23_4365677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_4365677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365677 prefixEnd_4365677 := by exact prefixLift 4365677
  have htrace : WordTrace (prefixWord ++ tailWord_4365677) baseStart_4365677 baseEnd_4365677 := by
    simpa [prefixWord, tailWord_4365677, baseEnd_4365677] using wordTrace_append hprefix tailTrace_4365677
  have hstable : (prefixWord ++ tailWord_4365677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365677).length < 2 ^ (prefixWord ++ tailWord_4365677).sum := by decide
  have hdescent : baseEnd_4365677 < baseStart_4365677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365713 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_4365713 : Nat := 118140960795 + 4365713 * 2 ^ 59
def prefixEnd_4365713 : Nat := 4983230072969 + 3 ^ 40 * 4365713 * 2
def baseEnd_4365713 : Nat := 2241709168582182861509957

theorem tailTrace_4365713 : CollatzResearch.WordTrace tailWord_4365713 prefixEnd_4365713 2241709168582182861509957 := by
  unfold tailWord_4365713
  simp only [CollatzResearch.WordTrace]
  refine ⟨159230634432774880264909793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106153756288516586843273195 159230634432774880264909793)
  ·
    refine ⟨119422975824581160198682345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159230634432774880264909793 119422975824581160198682345)
    ·
      refine ⟨89567231868435870149011759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119422975824581160198682345 89567231868435870149011759)
      ·
        refine ⟨134350847802653805223517639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89567231868435870149011759 134350847802653805223517639)
        ·
          refine ⟨201526271703980707835276459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134350847802653805223517639 201526271703980707835276459)
          ·
            refine ⟨302289407555971061752914689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201526271703980707835276459 302289407555971061752914689)
            ·
              refine ⟨226717055666978296314686017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302289407555971061752914689 226717055666978296314686017)
              ·
                refine ⟨170037791750233722236014513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226717055666978296314686017 170037791750233722236014513)
                ·
                  refine ⟨127528343812675291677010885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170037791750233722236014513 127528343812675291677010885)
                  ·
                    refine ⟨23911564464876617189439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127528343812675291677010885 23911564464876617189439541)
                    ·
                      refine ⟨2241709168582182861509957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23911564464876617189439541 2241709168582182861509957)
                      ·
                        rfl

theorem cell23_4365713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_4365713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365713 prefixEnd_4365713 := by exact prefixLift 4365713
  have htrace : WordTrace (prefixWord ++ tailWord_4365713) baseStart_4365713 baseEnd_4365713 := by
    simpa [prefixWord, tailWord_4365713, baseEnd_4365713] using wordTrace_append hprefix tailTrace_4365713
  have hstable : (prefixWord ++ tailWord_4365713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365713).length < 2 ^ (prefixWord ++ tailWord_4365713).sum := by decide
  have hdescent : baseEnd_4365713 < baseStart_4365713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365717 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_4365717 : Nat := 118140960795 + 4365717 * 2 ^ 59
def prefixEnd_4365717 : Nat := 4983230072969 + 3 ^ 40 * 4365717 * 2
def baseEnd_4365717 : Nat := 2241711222504800845859939

theorem tailTrace_4365717 : CollatzResearch.WordTrace tailWord_4365717 prefixEnd_4365717 2241711222504800845859939 := by
  unfold tailWord_4365717
  simp only [CollatzResearch.WordTrace]
  refine ⟨159230780324760388948055405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106153853549840259298703603 159230780324760388948055405)
  ·
    refine ⟨59711542621785145855520777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159230780324760388948055405 59711542621785145855520777)
    ·
      refine ⟨44783656966338859391640583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59711542621785145855520777 44783656966338859391640583)
      ·
        refine ⟨67175485449508289087460875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44783656966338859391640583 67175485449508289087460875)
        ·
          refine ⟨100763228174262433631191313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67175485449508289087460875 100763228174262433631191313)
          ·
            refine ⟨75572421130696825223393485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100763228174262433631191313 75572421130696825223393485)
            ·
              refine ⟨28339657924011309458772557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75572421130696825223393485 28339657924011309458772557)
              ·
                refine ⟨10627371721504241047039709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28339657924011309458772557 10627371721504241047039709)
                ·
                  refine ⟨3985264395564090392639891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10627371721504241047039709 3985264395564090392639891)
                  ·
                    refine ⟨5977896593346135588959837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985264395564090392639891 5977896593346135588959837)
                    ·
                      refine ⟨2241711222504800845859939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5977896593346135588959837 2241711222504800845859939)
                      ·
                        rfl

theorem cell23_4365717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_4365717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365717 prefixEnd_4365717 := by exact prefixLift 4365717
  have htrace : WordTrace (prefixWord ++ tailWord_4365717) baseStart_4365717 baseEnd_4365717 := by
    simpa [prefixWord, tailWord_4365717, baseEnd_4365717] using wordTrace_append hprefix tailTrace_4365717
  have hstable : (prefixWord ++ tailWord_4365717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365717).length < 2 ^ (prefixWord ++ tailWord_4365717).sum := by decide
  have hdescent : baseEnd_4365717 < baseStart_4365717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365727 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4365727 : Nat := 118140960795 + 4365727 * 2 ^ 59
def prefixEnd_4365727 : Nat := 4983230072969 + 3 ^ 40 * 4365727 * 2
def baseEnd_4365727 : Nat := 2241716357311345806734893

theorem tailTrace_4365727 : CollatzResearch.WordTrace tailWord_4365727 prefixEnd_4365727 2241716357311345806734893 := by
  unfold tailWord_4365727
  simp only [CollatzResearch.WordTrace]
  refine ⟨159231145054724160655919435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106154096703149440437279623 159231145054724160655919435)
  ·
    refine ⟨238846717582086240983879153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159231145054724160655919435 238846717582086240983879153)
    ·
      refine ⟨179135038186564680737909365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238846717582086240983879153 179135038186564680737909365)
      ·
        refine ⟨16793909829990438819179003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179135038186564680737909365 16793909829990438819179003)
        ·
          refine ⟨25190864744985658228768505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16793909829990438819179003 25190864744985658228768505)
          ·
            refine ⟨18893148558739243671576379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25190864744985658228768505 18893148558739243671576379)
            ·
              refine ⟨28339722838108865507364569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18893148558739243671576379 28339722838108865507364569)
              ·
                refine ⟨21254792128581649130523427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28339722838108865507364569 21254792128581649130523427)
                ·
                  refine ⟨31882188192872473695785141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21254792128581649130523427 31882188192872473695785141)
                  ·
                    refine ⟨2988955143081794408979857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31882188192872473695785141 2988955143081794408979857)
                    ·
                      refine ⟨2241716357311345806734893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2988955143081794408979857 2241716357311345806734893)
                      ·
                        rfl

theorem cell23_4365727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4365727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365727 prefixEnd_4365727 := by exact prefixLift 4365727
  have htrace : WordTrace (prefixWord ++ tailWord_4365727) baseStart_4365727 baseEnd_4365727 := by
    simpa [prefixWord, tailWord_4365727, baseEnd_4365727] using wordTrace_append hprefix tailTrace_4365727
  have hstable : (prefixWord ++ tailWord_4365727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365727).length < 2 ^ (prefixWord ++ tailWord_4365727).sum := by decide
  have hdescent : baseEnd_4365727 < baseStart_4365727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365740 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_4365740 : Nat := 118140960795 + 4365740 * 2 ^ 59
def prefixEnd_4365740 : Nat := 4983230072969 + 3 ^ 40 * 4365740 * 2
def baseEnd_4365740 : Nat := 2241723032559854255872333

theorem tailTrace_4365740 : CollatzResearch.WordTrace tailWord_4365740 prefixEnd_4365740 2241723032559854255872333 := by
  unfold tailWord_4365740
  simp only [CollatzResearch.WordTrace]
  refine ⟨79615809601838531938071337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106154412802451375917428449 79615809601838531938071337)
  ·
    refine ⟨59711857201378898953553503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79615809601838531938071337 59711857201378898953553503)
    ·
      refine ⟨89567785802068348430330255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59711857201378898953553503 89567785802068348430330255)
      ·
        refine ⟨134351678703102522645495383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89567785802068348430330255 134351678703102522645495383)
        ·
          refine ⟨201527518054653783968243075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134351678703102522645495383 201527518054653783968243075)
          ·
            refine ⟨302291277081980675952364613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201527518054653783968243075 302291277081980675952364613)
            ·
              refine ⟨56679614452871376741068365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302291277081980675952364613 56679614452871376741068365)
              ·
                refine ⟨21254855419826766277900637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56679614452871376741068365 21254855419826766277900637)
                ·
                  refine ⟨7970570782435037354212739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21254855419826766277900637 7970570782435037354212739)
                  ·
                    refine ⟨11955856173652556031319109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7970570782435037354212739 11955856173652556031319109)
                    ·
                      refine ⟨2241723032559854255872333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11955856173652556031319109 2241723032559854255872333)
                      ·
                        rfl

theorem cell23_4365740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_4365740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365740 prefixEnd_4365740 := by exact prefixLift 4365740
  have htrace : WordTrace (prefixWord ++ tailWord_4365740) baseStart_4365740 baseEnd_4365740 := by
    simpa [prefixWord, tailWord_4365740, baseEnd_4365740] using wordTrace_append hprefix tailTrace_4365740
  have hstable : (prefixWord ++ tailWord_4365740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365740).length < 2 ^ (prefixWord ++ tailWord_4365740).sum := by decide
  have hdescent : baseEnd_4365740 < baseStart_4365740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365757 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_4365757 : Nat := 118140960795 + 4365757 * 2 ^ 59
def prefixEnd_4365757 : Nat := 4983230072969 + 3 ^ 40 * 4365757 * 2
def baseEnd_4365757 : Nat := 2241731761730980689359755

theorem tailTrace_4365757 : CollatzResearch.WordTrace tailWord_4365757 prefixEnd_4365757 2241731761730980689359755 := by
  unfold tailWord_4365757
  simp only [CollatzResearch.WordTrace]
  refine ⟨159232239244615475779511525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106154826163076983853007683 159232239244615475779511525)
  ·
    refine ⟨29856044858365401708658411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159232239244615475779511525 29856044858365401708658411)
    ·
      refine ⟨44784067287548102562987617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29856044858365401708658411 44784067287548102562987617)
      ·
        refine ⟨33588050465661076922240713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44784067287548102562987617 33588050465661076922240713)
        ·
          refine ⟨25191037849245807691680535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33588050465661076922240713 25191037849245807691680535)
          ·
            refine ⟨37786556773868711537520803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25191037849245807691680535 37786556773868711537520803)
            ·
              refine ⟨56679835160803067306281205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37786556773868711537520803 56679835160803067306281205)
              ·
                refine ⟨5313734546325287559963863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56679835160803067306281205 5313734546325287559963863)
                ·
                  refine ⟨7970601819487931339945795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313734546325287559963863 7970601819487931339945795)
                  ·
                    refine ⟨11955902729231897009918693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7970601819487931339945795 11955902729231897009918693)
                    ·
                      refine ⟨2241731761730980689359755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11955902729231897009918693 2241731761730980689359755)
                      ·
                        rfl

theorem cell23_4365757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_4365757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365757 prefixEnd_4365757 := by exact prefixLift 4365757
  have htrace : WordTrace (prefixWord ++ tailWord_4365757) baseStart_4365757 baseEnd_4365757 := by
    simpa [prefixWord, tailWord_4365757, baseEnd_4365757] using wordTrace_append hprefix tailTrace_4365757
  have hstable : (prefixWord ++ tailWord_4365757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365757).length < 2 ^ (prefixWord ++ tailWord_4365757).sum := by decide
  have hdescent : baseEnd_4365757 < baseStart_4365757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365760 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_4365760 : Nat := 118140960795 + 4365760 * 2 ^ 59
def prefixEnd_4365760 : Nat := 4983230072969 + 3 ^ 40 * 4365760 * 2
def baseEnd_4365760 : Nat := 2241733302172944177622241

theorem tailTrace_4365760 : CollatzResearch.WordTrace tailWord_4365760 prefixEnd_4365760 2241733302172944177622241 := by
  unfold tailWord_4365760
  simp only [CollatzResearch.WordTrace]
  refine ⟨79616174331802303645935367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106154899109069738194580489 79616174331802303645935367)
  ·
    refine ⟨119424261497703455468903051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79616174331802303645935367 119424261497703455468903051)
    ·
      refine ⟨179136392246555183203354577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119424261497703455468903051 179136392246555183203354577)
      ·
        refine ⟨134352294184916387402515933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179136392246555183203354577 134352294184916387402515933)
        ·
          refine ⟨50382110319343645275943475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134352294184916387402515933 50382110319343645275943475)
          ·
            refine ⟨75573165479015467913915213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50382110319343645275943475 75573165479015467913915213)
            ·
              refine ⟨28339937054630800467718205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75573165479015467913915213 28339937054630800467718205)
              ·
                refine ⟨10627476395486550175394327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28339937054630800467718205 10627476395486550175394327)
                ·
                  refine ⟨15941214593229825263091491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10627476395486550175394327 15941214593229825263091491)
                  ·
                    refine ⟨23911821889844737894637237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15941214593229825263091491 23911821889844737894637237)
                    ·
                      refine ⟨2241733302172944177622241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23911821889844737894637237 2241733302172944177622241)
                      ·
                        rfl

theorem cell23_4365760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_4365760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365760 prefixEnd_4365760 := by exact prefixLift 4365760
  have htrace : WordTrace (prefixWord ++ tailWord_4365760) baseStart_4365760 baseEnd_4365760 := by
    simpa [prefixWord, tailWord_4365760, baseEnd_4365760] using wordTrace_append hprefix tailTrace_4365760
  have hstable : (prefixWord ++ tailWord_4365760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365760).length < 2 ^ (prefixWord ++ tailWord_4365760).sum := by decide
  have hdescent : baseEnd_4365760 < baseStart_4365760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365762 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4365762 : Nat := 118140960795 + 4365762 * 2 ^ 59
def prefixEnd_4365762 : Nat := 4983230072969 + 3 ^ 40 * 4365762 * 2
def baseEnd_4365762 : Nat := 747244776378084389932411

theorem tailTrace_4365762 : CollatzResearch.WordTrace tailWord_4365762 prefixEnd_4365762 747244776378084389932411 := by
  unfold tailWord_4365762
  simp only [CollatzResearch.WordTrace]
  refine ⟨39808105402399340408360885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106154947739731574422295693 39808105402399340408360885)
  ·
    refine ⟨3732009881474938163283833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39808105402399340408360885 3732009881474938163283833)
    ·
      refine ⟨2799007411106203622462875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3732009881474938163283833 2799007411106203622462875)
      ·
        refine ⟨4198511116659305433694313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799007411106203622462875 4198511116659305433694313)
        ·
          refine ⟨3148883337494479075270735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4198511116659305433694313 3148883337494479075270735)
          ·
            refine ⟨4723325006241718612906103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148883337494479075270735 4723325006241718612906103)
            ·
              refine ⟨7084987509362577919359155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723325006241718612906103 7084987509362577919359155)
              ·
                refine ⟨10627481264043866879038733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084987509362577919359155 10627481264043866879038733)
                ·
                  refine ⟨3985305474016450079639525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10627481264043866879038733 3985305474016450079639525)
                  ·
                    refine ⟨747244776378084389932411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985305474016450079639525 747244776378084389932411)
                    ·
                      rfl

theorem cell23_4365762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4365762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365762 prefixEnd_4365762 := by exact prefixLift 4365762
  have htrace : WordTrace (prefixWord ++ tailWord_4365762) baseStart_4365762 baseEnd_4365762 := by
    simpa [prefixWord, tailWord_4365762, baseEnd_4365762] using wordTrace_append hprefix tailTrace_4365762
  have hstable : (prefixWord ++ tailWord_4365762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365762).length < 2 ^ (prefixWord ++ tailWord_4365762).sum := by decide
  have hdescent : baseEnd_4365762 < baseStart_4365762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365763 : List Nat := [1, 1, 1, 3, 1, 1, 15]
def baseStart_4365763 : Nat := 118140960795 + 4365763 * 2 ^ 59
def prefixEnd_4365763 : Nat := 4983230072969 + 3 ^ 40 * 4365763 * 2
def baseEnd_4365763 : Nat := 27675738797714909455367

theorem tailTrace_4365763 : CollatzResearch.WordTrace tailWord_4365763 prefixEnd_4365763 27675738797714909455367 := by
  unfold tailWord_4365763
  simp only [CollatzResearch.WordTrace]
  refine ⟨159232458082593738804229943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106154972055062492536153295 159232458082593738804229943)
  ·
    refine ⟨238848687123890608206344915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159232458082593738804229943 238848687123890608206344915)
    ·
      refine ⟨358273030685835912309517373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238848687123890608206344915 358273030685835912309517373)
      ·
        refine ⟨134352386507188467116069015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358273030685835912309517373 134352386507188467116069015)
        ·
          refine ⟨201528579760782700674103523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134352386507188467116069015 201528579760782700674103523)
          ·
            refine ⟨302292869641174051011155285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201528579760782700674103523 302292869641174051011155285)
            ·
              refine ⟨27675738797714909455367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 302292869641174051011155285 27675738797714909455367)
              ·
                rfl

theorem cell23_4365763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 15].length) (baseStart_4365763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365763 prefixEnd_4365763 := by exact prefixLift 4365763
  have htrace : WordTrace (prefixWord ++ tailWord_4365763) baseStart_4365763 baseEnd_4365763 := by
    simpa [prefixWord, tailWord_4365763, baseEnd_4365763] using wordTrace_append hprefix tailTrace_4365763
  have hstable : (prefixWord ++ tailWord_4365763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365763).length < 2 ^ (prefixWord ++ tailWord_4365763).sum := by decide
  have hdescent : baseEnd_4365763 < baseStart_4365763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365767 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 2, 4]
def baseStart_4365767 : Nat := 118140960795 + 4365767 * 2 ^ 59
def prefixEnd_4365767 : Nat := 4983230072969 + 3 ^ 40 * 4365767 * 2
def baseEnd_4365767 : Nat := 747245632179175216744903

theorem tailTrace_4365767 : CollatzResearch.WordTrace tailWord_4365767 prefixEnd_4365767 747245632179175216744903 := by
  unfold tailWord_4365767
  simp only [CollatzResearch.WordTrace]
  refine ⟨159232603974579247487375555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106155069316386164991583703 159232603974579247487375555)
  ·
    refine ⟨238848905961868871231063333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159232603974579247487375555 238848905961868871231063333)
    ·
      refine ⟨44784169867850413355824375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238848905961868871231063333 44784169867850413355824375)
      ·
        refine ⟨67176254801775620033736563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44784169867850413355824375 67176254801775620033736563)
        ·
          refine ⟨100764382202663430050604845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67176254801775620033736563 100764382202663430050604845)
          ·
            refine ⟨37786643325998786268976817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100764382202663430050604845 37786643325998786268976817)
            ·
              refine ⟨28339982494499089701732613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37786643325998786268976817 28339982494499089701732613)
              ·
                refine ⟨5313746717718579319074865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28339982494499089701732613 5313746717718579319074865)
                ·
                  refine ⟨3985310038288934489306149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313746717718579319074865 3985310038288934489306149)
                  ·
                    refine ⟨747245632179175216744903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985310038288934489306149 747245632179175216744903)
                    ·
                      rfl

theorem cell23_4365767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_4365767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365767 prefixEnd_4365767 := by exact prefixLift 4365767
  have htrace : WordTrace (prefixWord ++ tailWord_4365767) baseStart_4365767 baseEnd_4365767 := by
    simpa [prefixWord, tailWord_4365767, baseEnd_4365767] using wordTrace_append hprefix tailTrace_4365767
  have hstable : (prefixWord ++ tailWord_4365767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365767).length < 2 ^ (prefixWord ++ tailWord_4365767).sum := by decide
  have hdescent : baseEnd_4365767 < baseStart_4365767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365770 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_4365770 : Nat := 118140960795 + 4365770 * 2 ^ 59
def prefixEnd_4365770 : Nat := 4983230072969 + 3 ^ 40 * 4365770 * 2
def baseEnd_4365770 : Nat := 2241738436979489138497195

theorem tailTrace_4365770 : CollatzResearch.WordTrace tailWord_4365770 prefixEnd_4365770 2241738436979489138497195 := by
  unfold tailWord_4365770
  simp only [CollatzResearch.WordTrace]
  refine ⟨39808178348392094749933691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106155142262378919333156509 39808178348392094749933691)
  ·
    refine ⟨59712267522588142124900537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39808178348392094749933691 59712267522588142124900537)
    ·
      refine ⟨44784200641941106593675403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59712267522588142124900537 44784200641941106593675403)
      ·
        refine ⟨67176300962911659890513105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44784200641941106593675403 67176300962911659890513105)
        ·
          refine ⟨50382225722183744917884829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67176300962911659890513105 50382225722183744917884829)
          ·
            refine ⟨18893334645818904344206811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50382225722183744917884829 18893334645818904344206811)
            ·
              refine ⟨28340001968728356516310217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18893334645818904344206811 28340001968728356516310217)
              ·
                refine ⟨21255001476546267387232663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28340001968728356516310217 21255001476546267387232663)
                ·
                  refine ⟨31882502214819401080848995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21255001476546267387232663 31882502214819401080848995)
                  ·
                    refine ⟨47823753322229101621273493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31882502214819401080848995 47823753322229101621273493)
                    ·
                      refine ⟨2241738436979489138497195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47823753322229101621273493 2241738436979489138497195)
                      ·
                        rfl

theorem cell23_4365770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_4365770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365770 prefixEnd_4365770 := by exact prefixLift 4365770
  have htrace : WordTrace (prefixWord ++ tailWord_4365770) baseStart_4365770 baseEnd_4365770 := by
    simpa [prefixWord, tailWord_4365770, baseEnd_4365770] using wordTrace_append hprefix tailTrace_4365770
  have hstable : (prefixWord ++ tailWord_4365770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365770).length < 2 ^ (prefixWord ++ tailWord_4365770).sum := by decide
  have hdescent : baseEnd_4365770 < baseStart_4365770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365784 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 2, 4]
def baseStart_4365784 : Nat := 118140960795 + 4365784 * 2 ^ 59
def prefixEnd_4365784 : Nat := 4983230072969 + 3 ^ 40 * 4365784 * 2
def baseEnd_4365784 : Nat := 747248541902884027907377

theorem tailTrace_4365784 : CollatzResearch.WordTrace tailWord_4365784 prefixEnd_4365784 747248541902884027907377 := by
  unfold tailWord_4365784
  simp only [CollatzResearch.WordTrace]
  refine ⟨79616612007758829695372203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106155482677011772927162937 79616612007758829695372203)
  ·
    refine ⟨119424918011638244543058305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79616612007758829695372203 119424918011638244543058305)
    ·
      refine ⟨89568688508728683407293729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119424918011638244543058305 89568688508728683407293729)
      ·
        refine ⟨67176516381546512555470297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89568688508728683407293729 67176516381546512555470297)
        ·
          refine ⟨50382387286159884416602723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67176516381546512555470297 50382387286159884416602723)
          ·
            refine ⟨75573580929239826624904085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50382387286159884416602723 75573580929239826624904085)
            ·
              refine ⟨3542511606058116873042379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75573580929239826624904085 3542511606058116873042379)
              ·
                refine ⟨5313767409087175309563569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542511606058116873042379 5313767409087175309563569)
                ·
                  refine ⟨3985325556815381482172677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313767409087175309563569 3985325556815381482172677)
                  ·
                    refine ⟨747248541902884027907377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985325556815381482172677 747248541902884027907377)
                    ·
                      rfl

theorem cell23_4365784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_4365784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365784 prefixEnd_4365784 := by exact prefixLift 4365784
  have htrace : WordTrace (prefixWord ++ tailWord_4365784) baseStart_4365784 baseEnd_4365784 := by
    simpa [prefixWord, tailWord_4365784, baseEnd_4365784] using wordTrace_append hprefix tailTrace_4365784
  have hstable : (prefixWord ++ tailWord_4365784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365784).length < 2 ^ (prefixWord ++ tailWord_4365784).sum := by decide
  have hdescent : baseEnd_4365784 < baseStart_4365784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365807 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 3]
def baseStart_4365807 : Nat := 118140960795 + 4365807 * 2 ^ 59
def prefixEnd_4365807 : Nat := 4983230072969 + 3 ^ 40 * 4365807 * 2
def baseEnd_4365807 : Nat := 2241757435763705493734525

theorem tailTrace_4365807 : CollatzResearch.WordTrace tailWord_4365807 prefixEnd_4365807 2241757435763705493734525 := by
  unfold tailWord_4365807
  simp only [CollatzResearch.WordTrace]
  refine ⟨159234062894434334318831675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106156041929622889545887783 159234062894434334318831675)
  ·
    refine ⟨238851094341651501478247513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159234062894434334318831675 238851094341651501478247513)
    ·
      refine ⟨179138320756238626108685635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238851094341651501478247513 179138320756238626108685635)
      ·
        refine ⟨268707481134357939163028453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179138320756238626108685635 268707481134357939163028453)
        ·
          refine ⟨50382652712692113593067835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268707481134357939163028453 50382652712692113593067835)
          ·
            refine ⟨75573979069038170389601753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50382652712692113593067835 75573979069038170389601753)
            ·
              refine ⟨56680484301778627792201315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75573979069038170389601753 56680484301778627792201315)
              ·
                refine ⟨85020726452667941688301973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56680484301778627792201315 85020726452667941688301973)
                ·
                  refine ⟨3985346552468809766639155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85020726452667941688301973 3985346552468809766639155)
                  ·
                    refine ⟨5978019828703214649958733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985346552468809766639155 5978019828703214649958733)
                    ·
                      refine ⟨2241757435763705493734525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978019828703214649958733 2241757435763705493734525)
                      ·
                        rfl

theorem cell23_4365807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_4365807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365807 prefixEnd_4365807 := by exact prefixLift 4365807
  have htrace : WordTrace (prefixWord ++ tailWord_4365807) baseStart_4365807 baseEnd_4365807 := by
    simpa [prefixWord, tailWord_4365807, baseEnd_4365807] using wordTrace_append hprefix tailTrace_4365807
  have hstable : (prefixWord ++ tailWord_4365807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365807).length < 2 ^ (prefixWord ++ tailWord_4365807).sum := by decide
  have hdescent : baseEnd_4365807 < baseStart_4365807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365820 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_4365820 : Nat := 118140960795 + 4365820 * 2 ^ 59
def prefixEnd_4365820 : Nat := 4983230072969 + 3 ^ 40 * 4365820 * 2
def baseEnd_4365820 : Nat := 2241764111012213942871965

theorem tailTrace_4365820 : CollatzResearch.WordTrace tailWord_4365820 prefixEnd_4365820 2241764111012213942871965 := by
  unfold tailWord_4365820
  simp only [CollatzResearch.WordTrace]
  refine ⟨79617268521693618769527457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106156358028924825026036609 79617268521693618769527457)
  ·
    refine ⟨59712951391270214077145593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79617268521693618769527457 59712951391270214077145593)
    ·
      refine ⟨44784713543452660557859195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59712951391270214077145593 44784713543452660557859195)
      ·
        refine ⟨67177070315178990836788793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44784713543452660557859195 67177070315178990836788793)
        ·
          refine ⟨50382802736384243127591595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67177070315178990836788793 50382802736384243127591595)
          ·
            refine ⟨75574204104576364691387393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50382802736384243127591595 75574204104576364691387393)
            ·
              refine ⟨56680653078432273518540545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75574204104576364691387393 56680653078432273518540545)
              ·
                refine ⟨42510489808824205138905409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56680653078432273518540545 42510489808824205138905409)
                ·
                  refine ⟨31882867356618153854179057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42510489808824205138905409 31882867356618153854179057)
                  ·
                    refine ⟨23912150517463615390634293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31882867356618153854179057 23912150517463615390634293)
                    ·
                      refine ⟨2241764111012213942871965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23912150517463615390634293 2241764111012213942871965)
                      ·
                        rfl

theorem cell23_4365820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_4365820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365820 prefixEnd_4365820 := by exact prefixLift 4365820
  have htrace : WordTrace (prefixWord ++ tailWord_4365820) baseStart_4365820 baseEnd_4365820 := by
    simpa [prefixWord, tailWord_4365820, baseEnd_4365820] using wordTrace_append hprefix tailTrace_4365820
  have hstable : (prefixWord ++ tailWord_4365820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365820).length < 2 ^ (prefixWord ++ tailWord_4365820).sum := by decide
  have hdescent : baseEnd_4365820 < baseStart_4365820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365834 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_4365834 : Nat := 118140960795 + 4365834 * 2 ^ 59
def prefixEnd_4365834 : Nat := 4983230072969 + 3 ^ 40 * 4365834 * 2
def baseEnd_4365834 : Nat := 2241771299741376888096901

theorem tailTrace_4365834 : CollatzResearch.WordTrace tailWord_4365834 prefixEnd_4365834 2241771299741376888096901 := by
  unfold tailWord_4365834
  simp only [CollatzResearch.WordTrace]
  refine ⟨39808761916334129482516139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106156698443557678620043037 39808761916334129482516139)
  ·
    refine ⟨59713142874501194223774209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39808761916334129482516139 59713142874501194223774209)
    ·
      refine ⟨44784857155875895667830657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59713142874501194223774209 44784857155875895667830657)
      ·
        refine ⟨33588642866906921750872993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44784857155875895667830657 33588642866906921750872993)
        ·
          refine ⟨25191482150180191313154745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33588642866906921750872993 25191482150180191313154745)
          ·
            refine ⟨18893611612635143484866059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25191482150180191313154745 18893611612635143484866059)
            ·
              refine ⟨28340417418952715227299089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18893611612635143484866059 28340417418952715227299089)
              ·
                refine ⟨21255313064214536420474317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28340417418952715227299089 21255313064214536420474317)
                ·
                  refine ⟨7970742399080451157677869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21255313064214536420474317 7970742399080451157677869)
                  ·
                    refine ⟨2989028399655169184129201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7970742399080451157677869 2989028399655169184129201)
                    ·
                      refine ⟨2241771299741376888096901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989028399655169184129201 2241771299741376888096901)
                      ·
                        rfl

theorem cell23_4365834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_4365834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365834 prefixEnd_4365834 := by exact prefixLift 4365834
  have htrace : WordTrace (prefixWord ++ tailWord_4365834) baseStart_4365834 baseEnd_4365834 := by
    simpa [prefixWord, tailWord_4365834, baseEnd_4365834] using wordTrace_append hprefix tailTrace_4365834
  have hstable : (prefixWord ++ tailWord_4365834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365834).length < 2 ^ (prefixWord ++ tailWord_4365834).sum := by decide
  have hdescent : baseEnd_4365834 < baseStart_4365834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365877 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4365877 : Nat := 118140960795 + 4365877 * 2 ^ 59
def prefixEnd_4365877 : Nat := 4983230072969 + 3 ^ 40 * 4365877 * 2
def baseEnd_4365877 : Nat := 2241793379409520219859203

theorem tailTrace_4365877 : CollatzResearch.WordTrace tailWord_4365877 prefixEnd_4365877 2241793379409520219859203 := by
  unfold tailWord_4365877
  simp only [CollatzResearch.WordTrace]
  refine ⟨159236616004180736273879885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106157744002787157515919923 159236616004180736273879885)
  ·
    refine ⟨59713731001567776102704957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159236616004180736273879885 59713731001567776102704957)
    ·
      refine ⟨22392649125587916038514359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59713731001567776102704957 22392649125587916038514359)
      ·
        refine ⟨33588973688381874057771539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22392649125587916038514359 33588973688381874057771539)
        ·
          refine ⟨50383460532572811086657309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33588973688381874057771539 50383460532572811086657309)
          ·
            refine ⟨18893797699714804157496491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50383460532572811086657309 18893797699714804157496491)
            ·
              refine ⟨28340696549572206236244737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18893797699714804157496491 28340696549572206236244737)
              ·
                refine ⟨21255522412179154677183553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28340696549572206236244737 21255522412179154677183553)
                ·
                  refine ⟨15941641809134366007887665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21255522412179154677183553 15941641809134366007887665)
                  ·
                    refine ⟨11956231356850774505915749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15941641809134366007887665 11956231356850774505915749)
                    ·
                      refine ⟨2241793379409520219859203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11956231356850774505915749 2241793379409520219859203)
                      ·
                        rfl

theorem cell23_4365877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4365877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365877 prefixEnd_4365877 := by exact prefixLift 4365877
  have htrace : WordTrace (prefixWord ++ tailWord_4365877) baseStart_4365877 baseEnd_4365877 := by
    simpa [prefixWord, tailWord_4365877, baseEnd_4365877] using wordTrace_append hprefix tailTrace_4365877
  have hstable : (prefixWord ++ tailWord_4365877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365877).length < 2 ^ (prefixWord ++ tailWord_4365877).sum := by decide
  have hdescent : baseEnd_4365877 < baseStart_4365877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365881 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4365881 : Nat := 118140960795 + 4365881 * 2 ^ 59
def prefixEnd_4365881 : Nat := 4983230072969 + 3 ^ 40 * 4365881 * 2
def baseEnd_4365881 : Nat := 2241795433332138204209185

theorem tailTrace_4365881 : CollatzResearch.WordTrace tailWord_4365881 prefixEnd_4365881 2241795433332138204209185 := by
  unfold tailWord_4365881
  simp only [CollatzResearch.WordTrace]
  refine ⟨159236761896166244957025497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106157841264110829971350331 159236761896166244957025497)
  ·
    refine ⟨119427571422124683717769123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159236761896166244957025497 119427571422124683717769123)
    ·
      refine ⟨179141357133187025576653685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119427571422124683717769123 179141357133187025576653685)
      ·
        refine ⟨16794502231236283647811283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179141357133187025576653685 16794502231236283647811283)
        ·
          refine ⟨25191753346854425471716925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16794502231236283647811283 25191753346854425471716925)
          ·
            refine ⟨9446907505070409551893847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25191753346854425471716925 9446907505070409551893847)
            ·
              refine ⟨14170361257605614327840771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446907505070409551893847 14170361257605614327840771)
              ·
                refine ⟨21255541886408421491761157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14170361257605614327840771 21255541886408421491761157)
                ·
                  refine ⟨3985414103701579029705217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21255541886408421491761157 3985414103701579029705217)
                  ·
                    refine ⟨2989060577776184272278913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985414103701579029705217 2989060577776184272278913)
                    ·
                      refine ⟨2241795433332138204209185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989060577776184272278913 2241795433332138204209185)
                      ·
                        rfl

theorem cell23_4365881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4365881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365881 prefixEnd_4365881 := by exact prefixLift 4365881
  have htrace : WordTrace (prefixWord ++ tailWord_4365881) baseStart_4365881 baseEnd_4365881 := by
    simpa [prefixWord, tailWord_4365881, baseEnd_4365881] using wordTrace_append hprefix tailTrace_4365881
  have hstable : (prefixWord ++ tailWord_4365881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365881).length < 2 ^ (prefixWord ++ tailWord_4365881).sum := by decide
  have hdescent : baseEnd_4365881 < baseStart_4365881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365887 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 7]
def baseStart_4365887 : Nat := 118140960795 + 4365887 * 2 ^ 59
def prefixEnd_4365887 : Nat := 4983230072969 + 3 ^ 40 * 4365887 * 2
def baseEnd_4365887 : Nat := 249088723801785020081573

theorem tailTrace_4365887 : CollatzResearch.WordTrace tailWord_4365887 prefixEnd_4365887 249088723801785020081573 := by
  unfold tailWord_4365887
  simp only [CollatzResearch.WordTrace]
  refine ⟨159236980734144507981743915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106157987156096338654495943 159236980734144507981743915)
  ·
    refine ⟨238855471101216761972615873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159236980734144507981743915 238855471101216761972615873)
    ·
      refine ⟨179141603325912571479461905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238855471101216761972615873 179141603325912571479461905)
      ·
        refine ⟨134356202494434428609596429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179141603325912571479461905 134356202494434428609596429)
        ·
          refine ⟨50383575935412910728598661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134356202494434428609596429 50383575935412910728598661)
          ·
            refine ⟨9446920487889920761612249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50383575935412910728598661 9446920487889920761612249)
            ·
              refine ⟨7085190365917440571209187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9446920487889920761612249 7085190365917440571209187)
              ·
                refine ⟨10627785548876160856813781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085190365917440571209187 10627785548876160856813781)
                ·
                  refine ⟨249088723801785020081573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10627785548876160856813781 249088723801785020081573)
                  ·
                    rfl

theorem cell23_4365887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 7].length) (baseStart_4365887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365887 prefixEnd_4365887 := by exact prefixLift 4365887
  have htrace : WordTrace (prefixWord ++ tailWord_4365887) baseStart_4365887 baseEnd_4365887 := by
    simpa [prefixWord, tailWord_4365887, baseEnd_4365887] using wordTrace_append hprefix tailTrace_4365887
  have hstable : (prefixWord ++ tailWord_4365887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365887).length < 2 ^ (prefixWord ++ tailWord_4365887).sum := by decide
  have hdescent : baseEnd_4365887 < baseStart_4365887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365898 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_4365898 : Nat := 118140960795 + 4365898 * 2 ^ 59
def prefixEnd_4365898 : Nat := 4983230072969 + 3 ^ 40 * 4365898 * 2
def baseEnd_4365898 : Nat := 2241804162503264637696607

theorem tailTrace_4365898 : CollatzResearch.WordTrace tailWord_4365898 prefixEnd_4365898 2241804162503264637696607 := by
  unfold tailWord_4365898
  simp only [CollatzResearch.WordTrace]
  refine ⟨39809345484276164215098587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106158254624736437906929565 39809345484276164215098587)
  ·
    refine ⟨59714018226414246322647881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39809345484276164215098587 59714018226414246322647881)
    ·
      refine ⟨44785513669810684741985911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59714018226414246322647881 44785513669810684741985911)
      ·
        refine ⟨67178270504716027112978867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44785513669810684741985911 67178270504716027112978867)
        ·
          refine ⟨100767405757074040669468301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67178270504716027112978867 100767405757074040669468301)
          ·
            refine ⟨37787777158902765251050613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100767405757074040669468301 37787777158902765251050613)
            ·
              refine ⟨3542604108647134242285995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37787777158902765251050613 3542604108647134242285995)
              ·
                refine ⟨5313906162970701363428993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542604108647134242285995 5313906162970701363428993)
                ·
                  refine ⟨3985429622228026022571745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313906162970701363428993 3985429622228026022571745)
                  ·
                    refine ⟨2989072216671019516928809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985429622228026022571745 2989072216671019516928809)
                    ·
                      refine ⟨2241804162503264637696607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989072216671019516928809 2241804162503264637696607)
                      ·
                        rfl

theorem cell23_4365898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_4365898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365898 prefixEnd_4365898 := by exact prefixLift 4365898
  have htrace : WordTrace (prefixWord ++ tailWord_4365898) baseStart_4365898 baseEnd_4365898 := by
    simpa [prefixWord, tailWord_4365898, baseEnd_4365898] using wordTrace_append hprefix tailTrace_4365898
  have hstable : (prefixWord ++ tailWord_4365898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365898).length < 2 ^ (prefixWord ++ tailWord_4365898).sum := by decide
  have hdescent : baseEnd_4365898 < baseStart_4365898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4365981 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_4365981 : Nat := 118140960795 + 4365981 * 2 ^ 59
def prefixEnd_4365981 : Nat := 4983230072969 + 3 ^ 40 * 4365981 * 2
def baseEnd_4365981 : Nat := 747282260465862604319575

theorem tailTrace_4365981 : CollatzResearch.WordTrace tailWord_4365981 prefixEnd_4365981 747282260465862604319575 := by
  unfold tailWord_4365981
  simp only [CollatzResearch.WordTrace]
  refine ⟨159240409195803962035665797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106160272797202641357110531 159240409195803962035665797)
  ·
    refine ⟨29857576724213242881687337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159240409195803962035665797 29857576724213242881687337)
    ·
      refine ⟨22393182543159932161265503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29857576724213242881687337 22393182543159932161265503)
      ·
        refine ⟨33589773814739898241898255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22393182543159932161265503 33589773814739898241898255)
        ·
          refine ⟨50384660722109847362847383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33589773814739898241898255 50384660722109847362847383)
          ·
            refine ⟨75576991083164771044271075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50384660722109847362847383 75576991083164771044271075)
            ·
              refine ⟨113365486624747156566406613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75576991083164771044271075 113365486624747156566406613)
              ·
                refine ⟨2657003592767511482025155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113365486624747156566406613 2657003592767511482025155)
                ·
                  refine ⟨3985505389151267223037733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657003592767511482025155 3985505389151267223037733)
                  ·
                    refine ⟨747282260465862604319575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985505389151267223037733 747282260465862604319575)
                    ·
                      rfl

theorem cell23_4365981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_4365981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4365981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4365981 prefixEnd_4365981 := by exact prefixLift 4365981
  have htrace : WordTrace (prefixWord ++ tailWord_4365981) baseStart_4365981 baseEnd_4365981 := by
    simpa [prefixWord, tailWord_4365981, baseEnd_4365981] using wordTrace_append hprefix tailTrace_4365981
  have hstable : (prefixWord ++ tailWord_4365981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4365981).length < 2 ^ (prefixWord ++ tailWord_4365981).sum := by decide
  have hdescent : baseEnd_4365981 < baseStart_4365981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4365981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366024 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 1, 5]
def baseStart_4366024 : Nat := 118140960795 + 4366024 * 2 ^ 59
def prefixEnd_4366024 : Nat := 4983230072969 + 3 ^ 40 * 4366024 * 2
def baseEnd_4366024 : Nat := 747289620355243714907009

theorem tailTrace_4366024 : CollatzResearch.WordTrace tailWord_4366024 prefixEnd_4366024 747289620355243714907009 := by
  unfold tailWord_4366024
  simp only [CollatzResearch.WordTrace]
  refine ⟨79620988767324090189740563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106161318356432120252987417 79620988767324090189740563)
  ·
    refine ⟨119431483150986135284610845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79620988767324090189740563 119431483150986135284610845)
    ·
      refine ⟨44786806181619800731729067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119431483150986135284610845 44786806181619800731729067)
      ·
        refine ⟨67180209272429701097593601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44786806181619800731729067 67180209272429701097593601)
        ·
          refine ⟨50385156954322275823195201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67180209272429701097593601 50385156954322275823195201)
          ·
            refine ⟨37788867715741706867396401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50385156954322275823195201 37788867715741706867396401)
            ·
              refine ⟨28341650786806280150547301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37788867715741706867396401 28341650786806280150547301)
              ·
                refine ⟨5314059522526177528227619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28341650786806280150547301 5314059522526177528227619)
                ·
                  refine ⟨7971089283789266292341429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314059522526177528227619 7971089283789266292341429)
                  ·
                    refine ⟨747289620355243714907009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7971089283789266292341429 747289620355243714907009)
                    ·
                      rfl

theorem cell23_4366024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_4366024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366024 prefixEnd_4366024 := by exact prefixLift 4366024
  have htrace : WordTrace (prefixWord ++ tailWord_4366024) baseStart_4366024 baseEnd_4366024 := by
    simpa [prefixWord, tailWord_4366024, baseEnd_4366024] using wordTrace_append hprefix tailTrace_4366024
  have hstable : (prefixWord ++ tailWord_4366024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366024).length < 2 ^ (prefixWord ++ tailWord_4366024).sum := by decide
  have hdescent : baseEnd_4366024 < baseStart_4366024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366041 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 1, 5]
def baseStart_4366041 : Nat := 118140960795 + 4366041 * 2 ^ 59
def prefixEnd_4366041 : Nat := 4983230072969 + 3 ^ 40 * 4366041 * 2
def baseEnd_4366041 : Nat := 747292530078952526069483

theorem tailTrace_4366041 : CollatzResearch.WordTrace tailWord_4366041 prefixEnd_4366041 747292530078952526069483 := by
  unfold tailWord_4366041
  simp only [CollatzResearch.WordTrace]
  refine ⟨159242597575586592282849977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106161731717057728188566651 159242597575586592282849977)
  ·
    refine ⟨119431948181689944212137483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159242597575586592282849977 119431948181689944212137483)
    ·
      refine ⟨179147922272534916318206225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119431948181689944212137483 179147922272534916318206225)
      ·
        refine ⟨134360941704401187238654669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179147922272534916318206225 134360941704401187238654669)
        ·
          refine ⟨50385353139150445214495501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134360941704401187238654669 50385353139150445214495501)
          ·
            refine ⟨18894507427181416955435813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50385353139150445214495501 18894507427181416955435813)
            ·
              refine ⟨3542720142596515679144215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18894507427181416955435813 3542720142596515679144215)
              ·
                refine ⟨5314080213894773518716323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542720142596515679144215 5314080213894773518716323)
                ·
                  refine ⟨7971120320842160278074485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314080213894773518716323 7971120320842160278074485)
                  ·
                    refine ⟨747292530078952526069483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7971120320842160278074485 747292530078952526069483)
                    ·
                      rfl

theorem cell23_4366041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_4366041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366041 prefixEnd_4366041 := by exact prefixLift 4366041
  have htrace : WordTrace (prefixWord ++ tailWord_4366041) baseStart_4366041 baseEnd_4366041 := by
    simpa [prefixWord, tailWord_4366041, baseEnd_4366041] using wordTrace_append hprefix tailTrace_4366041
  have hstable : (prefixWord ++ tailWord_4366041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366041).length < 2 ^ (prefixWord ++ tailWord_4366041).sum := by decide
  have hdescent : baseEnd_4366041 < baseStart_4366041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366045 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 6]
def baseStart_4366045 : Nat := 118140960795 + 4366045 * 2 ^ 59
def prefixEnd_4366045 : Nat := 4983230072969 + 3 ^ 40 * 4366045 * 2
def baseEnd_4366045 : Nat := 249097738239941729173159

theorem tailTrace_4366045 : CollatzResearch.WordTrace tailWord_4366045 prefixEnd_4366045 249097738239941729173159 := by
  unfold tailWord_4366045
  simp only [CollatzResearch.WordTrace]
  refine ⟨159242743467572100965995589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106161828978381400643997059 159242743467572100965995589)
  ·
    refine ⟨29858014400169768931124173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159242743467572100965995589 29858014400169768931124173)
    ·
      refine ⟨11196755400063663349171565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29858014400169768931124173 11196755400063663349171565)
      ·
        refine ⟨4198783275023873755939337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11196755400063663349171565 4198783275023873755939337)
        ·
          refine ⟨3149087456267905316954503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4198783275023873755939337 3149087456267905316954503)
          ·
            refine ⟨4723631184401857975431755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149087456267905316954503 4723631184401857975431755)
            ·
              refine ⟨7085446776602786963147633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723631184401857975431755 7085446776602786963147633)
              ·
                refine ⟨5314085082452090222360725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7085446776602786963147633 5314085082452090222360725)
                ·
                  refine ⟨249097738239941729173159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5314085082452090222360725 249097738239941729173159)
                  ·
                    rfl

theorem cell23_4366045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_4366045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366045 prefixEnd_4366045 := by exact prefixLift 4366045
  have htrace : WordTrace (prefixWord ++ tailWord_4366045) baseStart_4366045 baseEnd_4366045 := by
    simpa [prefixWord, tailWord_4366045, baseEnd_4366045] using wordTrace_append hprefix tailTrace_4366045
  have hstable : (prefixWord ++ tailWord_4366045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366045).length < 2 ^ (prefixWord ++ tailWord_4366045).sum := by decide
  have hdescent : baseEnd_4366045 < baseStart_4366045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366055 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4366055 : Nat := 118140960795 + 4366055 * 2 ^ 59
def prefixEnd_4366055 : Nat := 4983230072969 + 3 ^ 40 * 4366055 * 2
def baseEnd_4366055 : Nat := 2241884778966020523433385

theorem tailTrace_4366055 : CollatzResearch.WordTrace tailWord_4366055 prefixEnd_4366055 2241884778966020523433385 := by
  unfold tailWord_4366055
  simp only [CollatzResearch.WordTrace]
  refine ⟨159243108197535872673859619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106162072131690581782573079 159243108197535872673859619)
  ·
    refine ⟨238864662296303809010789429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159243108197535872673859619 238864662296303809010789429)
    ·
      refine ⟨22393562090278482094761509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238864662296303809010789429 22393562090278482094761509)
      ·
        refine ⟨4198792891927215392767783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22393562090278482094761509 4198792891927215392767783)
        ·
          refine ⟨6298189337890823089151675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198792891927215392767783 6298189337890823089151675)
          ·
            refine ⟨9447284006836234633727513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298189337890823089151675 9447284006836234633727513)
            ·
              refine ⟨7085463005127175975295635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9447284006836234633727513 7085463005127175975295635)
              ·
                refine ⟨10628194507690763962943453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085463005127175975295635 10628194507690763962943453)
                ·
                  refine ⟨3985572940384036486103795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10628194507690763962943453 3985572940384036486103795)
                  ·
                    refine ⟨5978359410576054729155693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985572940384036486103795 5978359410576054729155693)
                    ·
                      refine ⟨2241884778966020523433385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978359410576054729155693 2241884778966020523433385)
                      ·
                        rfl

theorem cell23_4366055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4366055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366055 prefixEnd_4366055 := by exact prefixLift 4366055
  have htrace : WordTrace (prefixWord ++ tailWord_4366055) baseStart_4366055 baseEnd_4366055 := by
    simpa [prefixWord, tailWord_4366055, baseEnd_4366055] using wordTrace_append hprefix tailTrace_4366055
  have hstable : (prefixWord ++ tailWord_4366055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366055).length < 2 ^ (prefixWord ++ tailWord_4366055).sum := by decide
  have hdescent : baseEnd_4366055 < baseStart_4366055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366057 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_4366057 : Nat := 118140960795 + 4366057 * 2 ^ 59
def prefixEnd_4366057 : Nat := 4983230072969 + 3 ^ 40 * 4366057 * 2
def baseEnd_4366057 : Nat := 2241885805927329515608375

theorem tailTrace_4366057 : CollatzResearch.WordTrace tailWord_4366057 prefixEnd_4366057 2241885805927329515608375 := by
  unfold tailWord_4366057
  simp only [CollatzResearch.WordTrace]
  refine ⟨159243181143528627015432425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106162120762352418010288283 159243181143528627015432425)
  ·
    refine ⟨119432385857646470261574319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159243181143528627015432425 119432385857646470261574319)
    ·
      refine ⟨179148578786469705392361479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119432385857646470261574319 179148578786469705392361479)
      ·
        refine ⟨268722868179704558088542219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179148578786469705392361479 268722868179704558088542219)
        ·
          refine ⟨403084302269556837132813329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268722868179704558088542219 403084302269556837132813329)
          ·
            refine ⟨302313226702167627849609997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403084302269556837132813329 302313226702167627849609997)
            ·
              refine ⟨113367460013312860443603749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302313226702167627849609997 113367460013312860443603749)
              ·
                refine ⟨21256398752496161333175703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113367460013312860443603749 21256398752496161333175703)
                ·
                  refine ⟨31884598128744241999763555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21256398752496161333175703 31884598128744241999763555)
                  ·
                    refine ⟨47826897193116362999645333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31884598128744241999763555 47826897193116362999645333)
                    ·
                      refine ⟨2241885805927329515608375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47826897193116362999645333 2241885805927329515608375)
                      ·
                        rfl

theorem cell23_4366057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_4366057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366057 prefixEnd_4366057 := by exact prefixLift 4366057
  have htrace : WordTrace (prefixWord ++ tailWord_4366057) baseStart_4366057 baseEnd_4366057 := by
    simpa [prefixWord, tailWord_4366057, baseEnd_4366057] using wordTrace_append hprefix tailTrace_4366057
  have hstable : (prefixWord ++ tailWord_4366057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366057).length < 2 ^ (prefixWord ++ tailWord_4366057).sum := by decide
  have hdescent : baseEnd_4366057 < baseStart_4366057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366064 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_4366064 : Nat := 118140960795 + 4366064 * 2 ^ 59
def prefixEnd_4366064 : Nat := 4983230072969 + 3 ^ 40 * 4366064 * 2
def baseEnd_4366064 : Nat := 2241889400291910988220843

theorem tailTrace_4366064 : CollatzResearch.WordTrace tailWord_4366064 prefixEnd_4366064 2241889400291910988220843 := by
  unfold tailWord_4366064
  simp only [CollatzResearch.WordTrace]
  refine ⟨79621718227251633605468623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106162290969668844807291497 79621718227251633605468623)
  ·
    refine ⟨119432577340877450408202935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79621718227251633605468623 119432577340877450408202935)
    ·
      refine ⟨179148866011316175612304403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119432577340877450408202935 179148866011316175612304403)
      ·
        refine ⟨268723299016974263418456605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179148866011316175612304403 268723299016974263418456605)
        ·
          refine ⟨100771237131365348781921227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268723299016974263418456605 100771237131365348781921227)
          ·
            refine ⟨151156855697048023172881841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100771237131365348781921227 151156855697048023172881841)
            ·
              refine ⟨113367641772786017379661381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151156855697048023172881841 113367641772786017379661381)
              ·
                refine ⟨21256432832397378258686509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113367641772786017379661381 21256432832397378258686509)
                ·
                  refine ⟨7971162312149016847007441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21256432832397378258686509 7971162312149016847007441)
                  ·
                    refine ⟨5978371734111762635255581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7971162312149016847007441 5978371734111762635255581)
                    ·
                      refine ⟨2241889400291910988220843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978371734111762635255581 2241889400291910988220843)
                      ·
                        rfl

theorem cell23_4366064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_4366064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366064 prefixEnd_4366064 := by exact prefixLift 4366064
  have htrace : WordTrace (prefixWord ++ tailWord_4366064) baseStart_4366064 baseEnd_4366064 := by
    simpa [prefixWord, tailWord_4366064, baseEnd_4366064] using wordTrace_append hprefix tailTrace_4366064
  have hstable : (prefixWord ++ tailWord_4366064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366064).length < 2 ^ (prefixWord ++ tailWord_4366064).sum := by decide
  have hdescent : baseEnd_4366064 < baseStart_4366064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366081 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_4366081 : Nat := 118140960795 + 4366081 * 2 ^ 59
def prefixEnd_4366081 : Nat := 4983230072969 + 3 ^ 40 * 4366081 * 2
def baseEnd_4366081 : Nat := 2241898129463037421708265

theorem tailTrace_4366081 : CollatzResearch.WordTrace tailWord_4366081 prefixEnd_4366081 2241898129463037421708265 := by
  unfold tailWord_4366081
  simp only [CollatzResearch.WordTrace]
  refine ⟨159244056495441679114306097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106162704330294452742870731 159244056495441679114306097)
  ·
    refine ⟨119433042371581259335729573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159244056495441679114306097 119433042371581259335729573)
    ·
      refine ⟨22393695444671486125449295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119433042371581259335729573 22393695444671486125449295)
      ·
        refine ⟨33590543167007229188173943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22393695444671486125449295 33590543167007229188173943)
        ·
          refine ⟨50385814750510843782260915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33590543167007229188173943 50385814750510843782260915)
          ·
            refine ⟨75578722125766265673391373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50385814750510843782260915 75578722125766265673391373)
            ·
              refine ⟨28342020797162349627521765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75578722125766265673391373 28342020797162349627521765)
              ·
                refine ⟨5314128899467940555160331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28342020797162349627521765 5314128899467940555160331)
                ·
                  refine ⟨7971193349201910832740497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314128899467940555160331 7971193349201910832740497)
                  ·
                    refine ⟨5978395011901433124555373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7971193349201910832740497 5978395011901433124555373)
                    ·
                      refine ⟨2241898129463037421708265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978395011901433124555373 2241898129463037421708265)
                      ·
                        rfl

theorem cell23_4366081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_4366081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366081 prefixEnd_4366081 := by exact prefixLift 4366081
  have htrace : WordTrace (prefixWord ++ tailWord_4366081) baseStart_4366081 baseEnd_4366081 := by
    simpa [prefixWord, tailWord_4366081, baseEnd_4366081] using wordTrace_append hprefix tailTrace_4366081
  have hstable : (prefixWord ++ tailWord_4366081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366081).length < 2 ^ (prefixWord ++ tailWord_4366081).sum := by decide
  have hdescent : baseEnd_4366081 < baseStart_4366081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366084 : List Nat := [2, 3, 2, 2, 1, 3, 1, 9]
def baseStart_4366084 : Nat := 118140960795 + 4366084 * 2 ^ 59
def prefixEnd_4366084 : Nat := 4983230072969 + 3 ^ 40 * 4366084 * 2
def baseEnd_4366084 : Nat := 83033321107592626295213

theorem tailTrace_4366084 : CollatzResearch.WordTrace tailWord_4366084 prefixEnd_4366084 83033321107592626295213 := by
  unfold tailWord_4366084
  simp only [CollatzResearch.WordTrace]
  refine ⟨79622082957215405313332653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106162777276287207084443537 79622082957215405313332653)
  ·
    refine ⟨29858281108955776992499745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79622082957215405313332653 29858281108955776992499745)
    ·
      refine ⟨22393710831716832744374809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29858281108955776992499745 22393710831716832744374809)
      ·
        refine ⟨16795283123787624558281107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22393710831716832744374809 16795283123787624558281107)
        ·
          refine ⟨25192924685681436837421661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16795283123787624558281107 25192924685681436837421661)
          ·
            refine ⟨9447346757130538814033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25192924685681436837421661 9447346757130538814033123)
            ·
              refine ⟨14171020135695808221049685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447346757130538814033123 14171020135695808221049685)
              ·
                refine ⟨83033321107592626295213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14171020135695808221049685 83033321107592626295213)
                ·
                  rfl

theorem cell23_4366084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 9].length) (baseStart_4366084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366084 prefixEnd_4366084 := by exact prefixLift 4366084
  have htrace : WordTrace (prefixWord ++ tailWord_4366084) baseStart_4366084 baseEnd_4366084 := by
    simpa [prefixWord, tailWord_4366084, baseEnd_4366084] using wordTrace_append hprefix tailTrace_4366084
  have hstable : (prefixWord ++ tailWord_4366084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366084).length < 2 ^ (prefixWord ++ tailWord_4366084).sum := by decide
  have hdescent : baseEnd_4366084 < baseStart_4366084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366097 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_4366097 : Nat := 118140960795 + 4366097 * 2 ^ 59
def prefixEnd_4366097 : Nat := 4983230072969 + 3 ^ 40 * 4366097 * 2
def baseEnd_4366097 : Nat := 747302115051169786369397

theorem tailTrace_4366097 : CollatzResearch.WordTrace tailWord_4366097 prefixEnd_4366097 747302115051169786369397 := by
  unfold tailWord_4366097
  simp only [CollatzResearch.WordTrace]
  refine ⟨159244640063383713846888545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106163093375589142564592363 159244640063383713846888545)
  ·
    refine ⟨119433480047537785385166409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159244640063383713846888545 119433480047537785385166409)
    ·
      refine ⟨89575110035653339038874807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119433480047537785385166409 89575110035653339038874807)
      ·
        refine ⟨134362665053480008558312211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89575110035653339038874807 134362665053480008558312211)
        ·
          refine ⟨201543997580220012837468317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134362665053480008558312211 201543997580220012837468317)
          ·
            refine ⟨75578999092582504814050619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201543997580220012837468317 75578999092582504814050619)
            ·
              refine ⟨113368498638873757221075929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75578999092582504814050619 113368498638873757221075929)
              ·
                refine ⟨85026373979155317915806947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113368498638873757221075929 85026373979155317915806947)
                ·
                  refine ⟨127539560968732976873710421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85026373979155317915806947 127539560968732976873710421)
                  ·
                    refine ⟨747302115051169786369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127539560968732976873710421 747302115051169786369397)
                    ·
                      rfl

theorem cell23_4366097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_4366097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366097 prefixEnd_4366097 := by exact prefixLift 4366097
  have htrace : WordTrace (prefixWord ++ tailWord_4366097) baseStart_4366097 baseEnd_4366097 := by
    simpa [prefixWord, tailWord_4366097, baseEnd_4366097] using wordTrace_append hprefix tailTrace_4366097
  have hstable : (prefixWord ++ tailWord_4366097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366097).length < 2 ^ (prefixWord ++ tailWord_4366097).sum := by decide
  have hdescent : baseEnd_4366097 < baseStart_4366097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366098 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4366098 : Nat := 118140960795 + 4366098 * 2 ^ 59
def prefixEnd_4366098 : Nat := 4983230072969 + 3 ^ 40 * 4366098 * 2
def baseEnd_4366098 : Nat := 2241906858634163855195687

theorem tailTrace_4366098 : CollatzResearch.WordTrace tailWord_4366098 prefixEnd_4366098 2241906858634163855195687 := by
  unfold tailWord_4366098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811169134095022754418737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106163117690920060678449965 39811169134095022754418737)
  ·
    refine ⟨29858376850571267065814053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39811169134095022754418737 29858376850571267065814053)
    ·
      refine ⟨5598445659482112574840135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29858376850571267065814053 5598445659482112574840135)
      ·
        refine ⟨8397668489223168862260203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598445659482112574840135 8397668489223168862260203)
        ·
          refine ⟨12596502733834753293390305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8397668489223168862260203 12596502733834753293390305)
          ·
            refine ⟨9447377050376064970042729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12596502733834753293390305 9447377050376064970042729)
            ·
              refine ⟨7085532787782048727532047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9447377050376064970042729 7085532787782048727532047)
              ·
                refine ⟨10628299181673073091298071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085532787782048727532047 10628299181673073091298071)
                ·
                  refine ⟨15942448772509609636947107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10628299181673073091298071 15942448772509609636947107)
                  ·
                    refine ⟨23913673158764414455420661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15942448772509609636947107 23913673158764414455420661)
                    ·
                      refine ⟨2241906858634163855195687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23913673158764414455420661 2241906858634163855195687)
                      ·
                        rfl

theorem cell23_4366098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4366098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366098 prefixEnd_4366098 := by exact prefixLift 4366098
  have htrace : WordTrace (prefixWord ++ tailWord_4366098) baseStart_4366098 baseEnd_4366098 := by
    simpa [prefixWord, tailWord_4366098, baseEnd_4366098] using wordTrace_append hprefix tailTrace_4366098
  have hstable : (prefixWord ++ tailWord_4366098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366098).length < 2 ^ (prefixWord ++ tailWord_4366098).sum := by decide
  have hdescent : baseEnd_4366098 < baseStart_4366098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366111 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 3]
def baseStart_4366111 : Nat := 118140960795 + 4366111 * 2 ^ 59
def prefixEnd_4366111 : Nat := 4983230072969 + 3 ^ 40 * 4366111 * 2
def baseEnd_4366111 : Nat := 2241913533882672304333127

theorem tailTrace_4366111 : CollatzResearch.WordTrace tailWord_4366111 prefixEnd_4366111 2241913533882672304333127 := by
  unfold tailWord_4366111
  simp only [CollatzResearch.WordTrace]
  refine ⟨159245150685332994237898187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106163433790221996158598791 159245150685332994237898187)
  ·
    refine ⟨238867726027999491356847281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159245150685332994237898187 238867726027999491356847281)
    ·
      refine ⟨179150794520999618517635461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238867726027999491356847281 179150794520999618517635461)
      ·
        refine ⟨33590773972687428472056649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179150794520999618517635461 33590773972687428472056649)
        ·
          refine ⟨25193080479515571354042487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33590773972687428472056649 25193080479515571354042487)
          ·
            refine ⟨37789620719273357031063731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25193080479515571354042487 37789620719273357031063731)
            ·
              refine ⟨56684431078910035546595597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37789620719273357031063731 56684431078910035546595597)
              ·
                refine ⟨21256661654591263329973349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56684431078910035546595597 21256661654591263329973349)
                ·
                  refine ⟨3985624060235861874370003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21256661654591263329973349 3985624060235861874370003)
                  ·
                    refine ⟨5978436090353792811555005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985624060235861874370003 5978436090353792811555005)
                    ·
                      refine ⟨2241913533882672304333127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978436090353792811555005 2241913533882672304333127)
                      ·
                        rfl

theorem cell23_4366111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_4366111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366111 prefixEnd_4366111 := by exact prefixLift 4366111
  have htrace : WordTrace (prefixWord ++ tailWord_4366111) baseStart_4366111 baseEnd_4366111 := by
    simpa [prefixWord, tailWord_4366111, baseEnd_4366111] using wordTrace_append hprefix tailTrace_4366111
  have hstable : (prefixWord ++ tailWord_4366111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366111).length < 2 ^ (prefixWord ++ tailWord_4366111).sum := by decide
  have hdescent : baseEnd_4366111 < baseStart_4366111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366112 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4366112 : Nat := 118140960795 + 4366112 * 2 ^ 59
def prefixEnd_4366112 : Nat := 4983230072969 + 3 ^ 40 * 4366112 * 2
def baseEnd_4366112 : Nat := 2241914047363326800420623

theorem tailTrace_4366112 : CollatzResearch.WordTrace tailWord_4366112 prefixEnd_4366112 2241914047363326800420623 := by
  unfold tailWord_4366112
  simp only [CollatzResearch.WordTrace]
  refine ⟨79622593579164685704342295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106163458105552914272456393 79622593579164685704342295)
  ·
    refine ⟨119433890368747028556513443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79622593579164685704342295 119433890368747028556513443)
    ·
      refine ⟨179150835553120542834770165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119433890368747028556513443 179150835553120542834770165)
      ·
        refine ⟨16795390833105050890759703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179150835553120542834770165 16795390833105050890759703)
        ·
          refine ⟨25193086249657576336139555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16795390833105050890759703 25193086249657576336139555)
          ·
            refine ⟨37789629374486364504209333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25193086249657576336139555 37789629374486364504209333)
            ·
              refine ⟨3542777753858096672269625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37789629374486364504209333 3542777753858096672269625)
              ·
                refine ⟨2657083315393572504202219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542777753858096672269625 2657083315393572504202219)
                ·
                  refine ⟨3985624973090358756303329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657083315393572504202219 3985624973090358756303329)
                  ·
                    refine ⟨2989218729817769067227497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985624973090358756303329 2989218729817769067227497)
                    ·
                      refine ⟨2241914047363326800420623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989218729817769067227497 2241914047363326800420623)
                      ·
                        rfl

theorem cell23_4366112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4366112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366112 prefixEnd_4366112 := by exact prefixLift 4366112
  have htrace : WordTrace (prefixWord ++ tailWord_4366112) baseStart_4366112 baseEnd_4366112 := by
    simpa [prefixWord, tailWord_4366112, baseEnd_4366112] using wordTrace_append hprefix tailTrace_4366112
  have hstable : (prefixWord ++ tailWord_4366112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366112).length < 2 ^ (prefixWord ++ tailWord_4366112).sum := by decide
  have hdescent : baseEnd_4366112 < baseStart_4366112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366114 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4366114 : Nat := 118140960795 + 4366114 * 2 ^ 59
def prefixEnd_4366114 : Nat := 4983230072969 + 3 ^ 40 * 4366114 * 2
def baseEnd_4366114 : Nat := 747305024774878597531871

theorem tailTrace_4366114 : CollatzResearch.WordTrace tailWord_4366114 prefixEnd_4366114 747305024774878597531871 := by
  unfold tailWord_4366114
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811315026080531437564349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106163506736214750500171597 39811315026080531437564349)
  ·
    refine ⟨14929243134780199289086631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39811315026080531437564349 14929243134780199289086631)
    ·
      refine ⟨22393864702170298933629947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14929243134780199289086631 22393864702170298933629947)
      ·
        refine ⟨33590797053255448400444921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22393864702170298933629947 33590797053255448400444921)
        ·
          refine ⟨25193097789941586300333691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33590797053255448400444921 25193097789941586300333691)
          ·
            refine ⟨37789646684912379450500537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25193097789941586300333691 37789646684912379450500537)
            ·
              refine ⟨28342235013684284587875403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37789646684912379450500537 28342235013684284587875403)
              ·
                refine ⟨42513352520526426881813105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28342235013684284587875403 42513352520526426881813105)
                ·
                  refine ⟨31885014390394820161359829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42513352520526426881813105 31885014390394820161359829)
                  ·
                    refine ⟨747305024774878597531871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31885014390394820161359829 747305024774878597531871)
                    ·
                      rfl

theorem cell23_4366114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4366114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366114 prefixEnd_4366114 := by exact prefixLift 4366114
  have htrace : WordTrace (prefixWord ++ tailWord_4366114) baseStart_4366114 baseEnd_4366114 := by
    simpa [prefixWord, tailWord_4366114, baseEnd_4366114] using wordTrace_append hprefix tailTrace_4366114
  have hstable : (prefixWord ++ tailWord_4366114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366114).length < 2 ^ (prefixWord ++ tailWord_4366114).sum := by decide
  have hdescent : baseEnd_4366114 < baseStart_4366114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366138 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_4366138 : Nat := 118140960795 + 4366138 * 2 ^ 59
def prefixEnd_4366138 : Nat := 4983230072969 + 3 ^ 40 * 4366138 * 2
def baseEnd_4366138 : Nat := 2241927397860343698695503

theorem tailTrace_4366138 : CollatzResearch.WordTrace tailWord_4366138 prefixEnd_4366138 2241927397860343698695503 := by
  unfold tailWord_4366138
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811533864058794462282767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106164090304156785232754045 39811533864058794462282767)
  ·
    refine ⟨59717300796088191693424151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39811533864058794462282767 59717300796088191693424151)
    ·
      refine ⟨89575951194132287540136227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59717300796088191693424151 89575951194132287540136227)
      ·
        refine ⟨134363926791198431310204341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89575951194132287540136227 134363926791198431310204341)
        ·
          refine ⟨12596618136674852935331657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134363926791198431310204341 12596618136674852935331657)
          ·
            refine ⟨9447463602506139701498743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12596618136674852935331657 9447463602506139701498743)
            ·
              refine ⟨14171195403759209552248115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447463602506139701498743 14171195403759209552248115)
              ·
                refine ⟨21256793105638814328372173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14171195403759209552248115 21256793105638814328372173)
                ·
                  refine ⟨7971297414614555373139565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21256793105638814328372173 7971297414614555373139565)
                  ·
                    refine ⟨2989236530480458264927337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7971297414614555373139565 2989236530480458264927337)
                    ·
                      refine ⟨2241927397860343698695503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989236530480458264927337 2241927397860343698695503)
                      ·
                        rfl

theorem cell23_4366138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_4366138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366138 prefixEnd_4366138 := by exact prefixLift 4366138
  have htrace : WordTrace (prefixWord ++ tailWord_4366138) baseStart_4366138 baseEnd_4366138 := by
    simpa [prefixWord, tailWord_4366138, baseEnd_4366138] using wordTrace_append hprefix tailTrace_4366138
  have hstable : (prefixWord ++ tailWord_4366138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366138).length < 2 ^ (prefixWord ++ tailWord_4366138).sum := by decide
  have hdescent : baseEnd_4366138 < baseStart_4366138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366151 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_4366151 : Nat := 118140960795 + 4366151 * 2 ^ 59
def prefixEnd_4366151 : Nat := 4983230072969 + 3 ^ 40 * 4366151 * 2
def baseEnd_4366151 : Nat := 2241934073108852147832943

theorem tailTrace_4366151 : CollatzResearch.WordTrace tailWord_4366151 prefixEnd_4366151 2241934073108852147832943 := by
  unfold tailWord_4366151
  simp only [CollatzResearch.WordTrace]
  refine ⟨159246609605188081069354307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106164406403458720712902871 159246609605188081069354307)
  ·
    refine ⟨238869914407782121604031461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159246609605188081069354307 238869914407782121604031461)
    ·
      refine ⟨44788108951459147800755899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238869914407782121604031461 44788108951459147800755899)
      ·
        refine ⟨67182163427188721701133849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44788108951459147800755899 67182163427188721701133849)
        ·
          refine ⟨50386622570391541275850387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67182163427188721701133849 50386622570391541275850387)
          ·
            refine ⟨75579933855587311913775581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50386622570391541275850387 75579933855587311913775581)
            ·
              refine ⟨28342475195845241967665843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75579933855587311913775581 28342475195845241967665843)
              ·
                refine ⟨42513712793767862951498765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28342475195845241967665843 42513712793767862951498765)
                ·
                  refine ⟨15942642297662948606812037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42513712793767862951498765 15942642297662948606812037)
                  ·
                    refine ⟨2989245430811802863777257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15942642297662948606812037 2989245430811802863777257)
                    ·
                      refine ⟨2241934073108852147832943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989245430811802863777257 2241934073108852147832943)
                      ·
                        rfl

theorem cell23_4366151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_4366151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366151 prefixEnd_4366151 := by exact prefixLift 4366151
  have htrace : WordTrace (prefixWord ++ tailWord_4366151) baseStart_4366151 baseEnd_4366151 := by
    simpa [prefixWord, tailWord_4366151, baseEnd_4366151] using wordTrace_append hprefix tailTrace_4366151
  have hstable : (prefixWord ++ tailWord_4366151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366151).length < 2 ^ (prefixWord ++ tailWord_4366151).sum := by decide
  have hdescent : baseEnd_4366151 < baseStart_4366151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366154 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_4366154 : Nat := 118140960795 + 4366154 * 2 ^ 59
def prefixEnd_4366154 : Nat := 4983230072969 + 3 ^ 40 * 4366154 * 2
def baseEnd_4366154 : Nat := 2241935613550815636095429

theorem tailTrace_4366154 : CollatzResearch.WordTrace tailWord_4366154 prefixEnd_4366154 2241935613550815636095429 := by
  unfold tailWord_4366154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811679756044303145428379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106164479349451475054475677 39811679756044303145428379)
  ·
    refine ⟨59717519634066454718142569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39811679756044303145428379 59717519634066454718142569)
    ·
      refine ⟨44788139725549841038606927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59717519634066454718142569 44788139725549841038606927)
      ·
        refine ⟨67182209588324761557910391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44788139725549841038606927 67182209588324761557910391)
        ·
          refine ⟨100773314382487142336865587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67182209588324761557910391 100773314382487142336865587)
          ·
            refine ⟨151159971573730713505298381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100773314382487142336865587 151159971573730713505298381)
            ·
              refine ⟨56684989340149017564486893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151159971573730713505298381 56684989340149017564486893)
              ·
                refine ⟨21256871002555881586682585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56684989340149017564486893 21256871002555881586682585)
                ·
                  refine ⟨15942653251916911190011939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21256871002555881586682585 15942653251916911190011939)
                  ·
                    refine ⟨23913979877875366785017909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15942653251916911190011939 23913979877875366785017909)
                    ·
                      refine ⟨2241935613550815636095429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23913979877875366785017909 2241935613550815636095429)
                      ·
                        rfl

theorem cell23_4366154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_4366154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366154 prefixEnd_4366154 := by exact prefixLift 4366154
  have htrace : WordTrace (prefixWord ++ tailWord_4366154) baseStart_4366154 baseEnd_4366154 := by
    simpa [prefixWord, tailWord_4366154, baseEnd_4366154] using wordTrace_append hprefix tailTrace_4366154
  have hstable : (prefixWord ++ tailWord_4366154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366154).length < 2 ^ (prefixWord ++ tailWord_4366154).sum := by decide
  have hdescent : baseEnd_4366154 < baseStart_4366154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366224 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_4366224 : Nat := 118140960795 + 4366224 * 2 ^ 59
def prefixEnd_4366224 : Nat := 4983230072969 + 3 ^ 40 * 4366224 * 2
def baseEnd_4366224 : Nat := 2241971557196630362220107

theorem tailTrace_4366224 : CollatzResearch.WordTrace tailWord_4366224 prefixEnd_4366224 2241971557196630362220107 := by
  unfold tailWord_4366224
  simp only [CollatzResearch.WordTrace]
  refine ⟨79624636066961807268380863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106166181422615743024507817 79624636066961807268380863)
  ·
    refine ⟨119436954100442710902571295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79624636066961807268380863 119436954100442710902571295)
    ·
      refine ⟨179155431150664066353856943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119436954100442710902571295 179155431150664066353856943)
      ·
        refine ⟨268733146725996099530785415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179155431150664066353856943 268733146725996099530785415)
        ·
          refine ⟨403099720088994149296178123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268733146725996099530785415 403099720088994149296178123)
          ·
            refine ⟨604649580133491223944267185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403099720088994149296178123 604649580133491223944267185)
            ·
              refine ⟨453487185100118417958200389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604649580133491223944267185 453487185100118417958200389)
              ·
                refine ⟨85028847206272203367162573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453487185100118417958200389 85028847206272203367162573)
                ·
                  refine ⟨31885817702352076262685965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85028847206272203367162573 31885817702352076262685965)
                  ·
                    refine ⟨11957181638382028598507237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31885817702352076262685965 11957181638382028598507237)
                    ·
                      refine ⟨2241971557196630362220107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11957181638382028598507237 2241971557196630362220107)
                      ·
                        rfl

theorem cell23_4366224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_4366224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366224 prefixEnd_4366224 := by exact prefixLift 4366224
  have htrace : WordTrace (prefixWord ++ tailWord_4366224) baseStart_4366224 baseEnd_4366224 := by
    simpa [prefixWord, tailWord_4366224, baseEnd_4366224] using wordTrace_append hprefix tailTrace_4366224
  have hstable : (prefixWord ++ tailWord_4366224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366224).length < 2 ^ (prefixWord ++ tailWord_4366224).sum := by decide
  have hdescent : baseEnd_4366224 < baseStart_4366224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366264 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 10]
def baseStart_4366264 : Nat := 118140960795 + 4366264 * 2 ^ 59
def prefixEnd_4366264 : Nat := 4983230072969 + 3 ^ 40 * 4366264 * 2
def baseEnd_4366264 : Nat := 249110232935867800635547

theorem tailTrace_4366264 : CollatzResearch.WordTrace tailWord_4366264 prefixEnd_4366264 249110232935867800635547 := by
  unfold tailWord_4366264
  simp only [CollatzResearch.WordTrace]
  refine ⟨79625365526889350684108923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106167154035852467578811897 79625365526889350684108923)
  ·
    refine ⟨119438048290334026026163385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79625365526889350684108923 119438048290334026026163385)
    ·
      refine ⟨89578536217750519519622539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119438048290334026026163385 89578536217750519519622539)
      ·
        refine ⟨134367804326625779279433809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89578536217750519519622539 134367804326625779279433809)
        ·
          refine ⟨100775853244969334459575357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134367804326625779279433809 100775853244969334459575357)
          ·
            refine ⟨37790944966863500422340759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100775853244969334459575357 37790944966863500422340759)
            ·
              refine ⟨56686417450295250633511139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37790944966863500422340759 56686417450295250633511139)
              ·
                refine ⟨85029626175442875950266709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56686417450295250633511139 85029626175442875950266709)
                ·
                  refine ⟨249110232935867800635547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85029626175442875950266709 249110232935867800635547)
                  ·
                    rfl

theorem cell23_4366264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 10].length) (baseStart_4366264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366264 prefixEnd_4366264 := by exact prefixLift 4366264
  have htrace : WordTrace (prefixWord ++ tailWord_4366264) baseStart_4366264 baseEnd_4366264 := by
    simpa [prefixWord, tailWord_4366264, baseEnd_4366264] using wordTrace_append hprefix tailTrace_4366264
  have hstable : (prefixWord ++ tailWord_4366264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366264).length < 2 ^ (prefixWord ++ tailWord_4366264).sum := by decide
  have hdescent : baseEnd_4366264 < baseStart_4366264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366298 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_4366298 : Nat := 118140960795 + 4366298 * 2 ^ 59
def prefixEnd_4366298 : Nat := 4983230072969 + 3 ^ 40 * 4366298 * 2
def baseEnd_4366298 : Nat := 249112172751673674743863

theorem tailTrace_4366298 : CollatzResearch.WordTrace tailWord_4366298 prefixEnd_4366298 249112172751673674743863 := by
  unfold tailWord_4366298
  simp only [CollatzResearch.WordTrace]
  refine ⟨39812992783913881293738887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106167980757103683449970365 39812992783913881293738887)
  ·
    refine ⟨59719489175870821940608331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39812992783913881293738887 59719489175870821940608331)
    ·
      refine ⟨89579233763806232910912497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59719489175870821940608331 89579233763806232910912497)
      ·
        refine ⟨67184425322854674683184373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89579233763806232910912497 67184425322854674683184373)
        ·
          refine ⟨6298539874017625751548535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67184425322854674683184373 6298539874017625751548535)
          ·
            refine ⟨9447809811026438627322803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298539874017625751548535 9447809811026438627322803)
            ·
              refine ⟨14171714716539657940984205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447809811026438627322803 14171714716539657940984205)
              ·
                refine ⟨5314393018702371727869077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14171714716539657940984205 5314393018702371727869077)
                ·
                  refine ⟨249112172751673674743863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5314393018702371727869077 249112172751673674743863)
                  ·
                    rfl

theorem cell23_4366298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_4366298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366298 prefixEnd_4366298 := by exact prefixLift 4366298
  have htrace : WordTrace (prefixWord ++ tailWord_4366298) baseStart_4366298 baseEnd_4366298 := by
    simpa [prefixWord, tailWord_4366298, baseEnd_4366298] using wordTrace_append hprefix tailTrace_4366298
  have hstable : (prefixWord ++ tailWord_4366298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366298).length < 2 ^ (prefixWord ++ tailWord_4366298).sum := by decide
  have hdescent : baseEnd_4366298 < baseStart_4366298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366308 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_4366308 : Nat := 118140960795 + 4366308 * 2 ^ 59
def prefixEnd_4366308 : Nat := 4983230072969 + 3 ^ 40 * 4366308 * 2
def baseEnd_4366308 : Nat := 2242014689571608033569721

theorem tailTrace_4366308 : CollatzResearch.WordTrace tailWord_4366308 prefixEnd_4366308 2242014689571608033569721 := by
  unfold tailWord_4366308
  simp only [CollatzResearch.WordTrace]
  refine ⟨79626167932809648441409789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106168223910412864588546385 79626167932809648441409789)
  ·
    refine ⟨29859812974803618165528671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79626167932809648441409789 29859812974803618165528671)
    ·
      refine ⟨44789719462205427248293007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29859812974803618165528671 44789719462205427248293007)
      ·
        refine ⟨67184579193308140872439511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44789719462205427248293007 67184579193308140872439511)
        ·
          refine ⟨100776868789962211308659267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67184579193308140872439511 100776868789962211308659267)
          ·
            refine ⟨151165303184943316962988901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100776868789962211308659267 151165303184943316962988901)
            ·
              refine ⟨28343494347176871930560419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151165303184943316962988901 28343494347176871930560419)
              ·
                refine ⟨42515241520765307895840629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28343494347176871930560419 42515241520765307895840629)
                ·
                  refine ⟨3985803892571747615235059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42515241520765307895840629 3985803892571747615235059)
                  ·
                    refine ⟨5978705838857621422852589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985803892571747615235059 5978705838857621422852589)
                    ·
                      refine ⟨2242014689571608033569721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978705838857621422852589 2242014689571608033569721)
                      ·
                        rfl

theorem cell23_4366308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_4366308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366308 prefixEnd_4366308 := by exact prefixLift 4366308
  have htrace : WordTrace (prefixWord ++ tailWord_4366308) baseStart_4366308 baseEnd_4366308 := by
    simpa [prefixWord, tailWord_4366308, baseEnd_4366308] using wordTrace_append hprefix tailTrace_4366308
  have hstable : (prefixWord ++ tailWord_4366308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366308).length < 2 ^ (prefixWord ++ tailWord_4366308).sum := by decide
  have hdescent : baseEnd_4366308 < baseStart_4366308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366369 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_4366369 : Nat := 118140960795 + 4366369 * 2 ^ 59
def prefixEnd_4366369 : Nat := 4983230072969 + 3 ^ 40 * 4366369 * 2
def baseEnd_4366369 : Nat := 2242046011891532294906941

theorem tailTrace_4366369 : CollatzResearch.WordTrace tailWord_4366369 prefixEnd_4366369 2242046011891532294906941 := by
  unfold tailWord_4366369
  simp only [CollatzResearch.WordTrace]
  refine ⟨159254560718398304300790161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106169707145598869533860107 159254560718398304300790161)
  ·
    refine ⟨119440920538798728225592621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159254560718398304300790161 119440920538798728225592621)
    ·
      refine ⟨44790345202049523084597233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119440920538798728225592621 44790345202049523084597233)
      ·
        refine ⟨33592758901537142313447925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44790345202049523084597233 33592758901537142313447925)
        ·
          refine ⟨3149321147019107091885743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33592758901537142313447925 3149321147019107091885743)
          ·
            refine ⟨4723981720528660637828615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149321147019107091885743 4723981720528660637828615)
            ·
              refine ⟨7085972580792990956742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723981720528660637828615 7085972580792990956742923)
              ·
                refine ⟨10628958871189486435114385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085972580792990956742923 10628958871189486435114385)
                ·
                  refine ⟨7971719153392114826335789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10628958871189486435114385 7971719153392114826335789)
                  ·
                    refine ⟨2989394682522043059875921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7971719153392114826335789 2989394682522043059875921)
                    ·
                      refine ⟨2242046011891532294906941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989394682522043059875921 2242046011891532294906941)
                      ·
                        rfl

theorem cell23_4366369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_4366369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366369 prefixEnd_4366369 := by exact prefixLift 4366369
  have htrace : WordTrace (prefixWord ++ tailWord_4366369) baseStart_4366369 baseEnd_4366369 := by
    simpa [prefixWord, tailWord_4366369, baseEnd_4366369] using wordTrace_append hprefix tailTrace_4366369
  have hstable : (prefixWord ++ tailWord_4366369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366369).length < 2 ^ (prefixWord ++ tailWord_4366369).sum := by decide
  have hdescent : baseEnd_4366369 < baseStart_4366369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366376 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4366376 : Nat := 118140960795 + 4366376 * 2 ^ 59
def prefixEnd_4366376 : Nat := 4983230072969 + 3 ^ 40 * 4366376 * 2
def baseEnd_4366376 : Nat := 2242049606256113767519409

theorem tailTrace_4366376 : CollatzResearch.WordTrace tailWord_4366376 prefixEnd_4366376 2242049606256113767519409 := by
  unfold tailWord_4366376
  simp only [CollatzResearch.WordTrace]
  refine ⟨79627408014686472248147491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106169877352915296330863321 79627408014686472248147491)
  ·
    refine ⟨119441112022029708372221237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79627408014686472248147491 119441112022029708372221237)
    ·
      refine ⟨11197604252065285159895741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119441112022029708372221237 11197604252065285159895741)
      ·
        refine ⟨4199101594524481934960903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11197604252065285159895741 4199101594524481934960903)
        ·
          refine ⟨6298652391786722902441355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4199101594524481934960903 6298652391786722902441355)
          ·
            refine ⟨9447978587680084353662033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298652391786722902441355 9447978587680084353662033)
            ·
              refine ⟨7085983940760063265246525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9447978587680084353662033 7085983940760063265246525)
              ·
                refine ⟨2657243977785023724467447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7085983940760063265246525 2657243977785023724467447)
                ·
                  refine ⟨3985865966677535586701171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657243977785023724467447 3985865966677535586701171)
                  ·
                    refine ⟨5978798950016303380051757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3985865966677535586701171 5978798950016303380051757)
                    ·
                      refine ⟨2242049606256113767519409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978798950016303380051757 2242049606256113767519409)
                      ·
                        rfl

theorem cell23_4366376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4366376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366376 prefixEnd_4366376 := by exact prefixLift 4366376
  have htrace : WordTrace (prefixWord ++ tailWord_4366376) baseStart_4366376 baseEnd_4366376 := by
    simpa [prefixWord, tailWord_4366376, baseEnd_4366376] using wordTrace_append hprefix tailTrace_4366376
  have hstable : (prefixWord ++ tailWord_4366376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366376).length < 2 ^ (prefixWord ++ tailWord_4366376).sum := by decide
  have hdescent : baseEnd_4366376 < baseStart_4366376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366382 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4366382 : Nat := 118140960795 + 4366382 * 2 ^ 59
def prefixEnd_4366382 : Nat := 4983230072969 + 3 ^ 40 * 4366382 * 2
def baseEnd_4366382 : Nat := 2242052687140040744044381

theorem tailTrace_4366382 : CollatzResearch.WordTrace tailWord_4366382 prefixEnd_4366382 2242052687140040744044381 := by
  unfold tailWord_4366382
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906879358418900940126675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106170023244900805014008933 19906879358418900940126675)
  ·
    refine ⟨29860319037628351410190013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19906879358418900940126675 29860319037628351410190013)
    ·
      refine ⟨11197619639110631778821255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29860319037628351410190013 11197619639110631778821255)
      ·
        refine ⟨16796429458665947668231883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11197619639110631778821255 16796429458665947668231883)
        ·
          refine ⟨25194644187998921502347825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16796429458665947668231883 25194644187998921502347825)
          ·
            refine ⟨18895983140999191126760869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25194644187998921502347825 18895983140999191126760869)
            ·
              refine ⟨3542996838937348336267663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18895983140999191126760869 3542996838937348336267663)
              ·
                refine ⟨5314495258406022504401495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542996838937348336267663 5314495258406022504401495)
                ·
                  refine ⟨7971742887609033756602243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314495258406022504401495 7971742887609033756602243)
                  ·
                    refine ⟨11957614331413550634903365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7971742887609033756602243 11957614331413550634903365)
                    ·
                      refine ⟨2242052687140040744044381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11957614331413550634903365 2242052687140040744044381)
                      ·
                        rfl

theorem cell23_4366382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4366382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366382 prefixEnd_4366382 := by exact prefixLift 4366382
  have htrace : WordTrace (prefixWord ++ tailWord_4366382) baseStart_4366382 baseEnd_4366382 := by
    simpa [prefixWord, tailWord_4366382, baseEnd_4366382] using wordTrace_append hprefix tailTrace_4366382
  have hstable : (prefixWord ++ tailWord_4366382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366382).length < 2 ^ (prefixWord ++ tailWord_4366382).sum := by decide
  have hdescent : baseEnd_4366382 < baseStart_4366382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366385 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_4366385 : Nat := 118140960795 + 4366385 * 2 ^ 59
def prefixEnd_4366385 : Nat := 4983230072969 + 3 ^ 40 * 4366385 * 2
def baseEnd_4366385 : Nat := 2242054227582004232306867

theorem tailTrace_4366385 : CollatzResearch.WordTrace tailWord_4366385 prefixEnd_4366385 2242054227582004232306867 := by
  unfold tailWord_4366385
  simp only [CollatzResearch.WordTrace]
  refine ⟨159255144286340339033372609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106170096190893559355581739 159255144286340339033372609)
  ·
    refine ⟨119441358214755254275029457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159255144286340339033372609 119441358214755254275029457)
    ·
      refine ⟨89581018661066440706272093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119441358214755254275029457 89581018661066440706272093)
      ·
        refine ⟨33592881997899915264852035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89581018661066440706272093 33592881997899915264852035)
        ·
          refine ⟨50389322996849872897278053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33592881997899915264852035 50389322996849872897278053)
          ·
            refine ⟨9447998061909351168239635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50389322996849872897278053 9447998061909351168239635)
            ·
              refine ⟨14171997092864026752359453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447998061909351168239635 14171997092864026752359453)
              ·
                refine ⟨5314498909824010032134795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14171997092864026752359453 5314498909824010032134795)
                ·
                  refine ⟨7971748364736015048202193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314498909824010032134795 7971748364736015048202193)
                  ·
                    refine ⟨5978811273552011286151645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7971748364736015048202193 5978811273552011286151645)
                    ·
                      refine ⟨2242054227582004232306867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5978811273552011286151645 2242054227582004232306867)
                      ·
                        rfl

theorem cell23_4366385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_4366385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366385 prefixEnd_4366385 := by exact prefixLift 4366385
  have htrace : WordTrace (prefixWord ++ tailWord_4366385) baseStart_4366385 baseEnd_4366385 := by
    simpa [prefixWord, tailWord_4366385, baseEnd_4366385] using wordTrace_append hprefix tailTrace_4366385
  have hstable : (prefixWord ++ tailWord_4366385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366385).length < 2 ^ (prefixWord ++ tailWord_4366385).sum := by decide
  have hdescent : baseEnd_4366385 < baseStart_4366385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366392 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 2, 4]
def baseStart_4366392 : Nat := 118140960795 + 4366392 * 2 ^ 59
def prefixEnd_4366392 : Nat := 4983230072969 + 3 ^ 40 * 4366392 * 2
def baseEnd_4366392 : Nat := 747352607315528568306445

theorem tailTrace_4366392 : CollatzResearch.WordTrace tailWord_4366392 prefixEnd_4366392 747352607315528568306445 := by
  unfold tailWord_4366392
  simp only [CollatzResearch.WordTrace]
  refine ⟨79627699798657489614438715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106170266398209986152584953 79627699798657489614438715)
  ·
    refine ⟨119441549697986234421658073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79627699798657489614438715 119441549697986234421658073)
    ·
      refine ⟨89581162273489675816243555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119441549697986234421658073 89581162273489675816243555)
      ·
        refine ⟨134371743410234513724365333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89581162273489675816243555 134371743410234513724365333)
        ·
          refine ⟨6298675472354742830829625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134371743410234513724365333 6298675472354742830829625)
          ·
            refine ⟨4724006604266057123122219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6298675472354742830829625 4724006604266057123122219)
            ·
              refine ⟨7086009906399085684683329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724006604266057123122219 7086009906399085684683329)
              ·
                refine ⟨5314507429799314263512497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7086009906399085684683329 5314507429799314263512497)
                ·
                  refine ⟨3985880572349485697634373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5314507429799314263512497 3985880572349485697634373)
                  ·
                    refine ⟨747352607315528568306445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985880572349485697634373 747352607315528568306445)
                    ·
                      rfl

theorem cell23_4366392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_4366392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366392 prefixEnd_4366392 := by exact prefixLift 4366392
  have htrace : WordTrace (prefixWord ++ tailWord_4366392) baseStart_4366392 baseEnd_4366392 := by
    simpa [prefixWord, tailWord_4366392, baseEnd_4366392] using wordTrace_append hprefix tailTrace_4366392
  have hstable : (prefixWord ++ tailWord_4366392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366392).length < 2 ^ (prefixWord ++ tailWord_4366392).sum := by decide
  have hdescent : baseEnd_4366392 < baseStart_4366392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366408 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_4366408 : Nat := 118140960795 + 4366408 * 2 ^ 59
def prefixEnd_4366408 : Nat := 4983230072969 + 3 ^ 40 * 4366408 * 2
def baseEnd_4366408 : Nat := 2242066037637057642319261

theorem tailTrace_4366408 : CollatzResearch.WordTrace tailWord_4366408 prefixEnd_4366408 2242066037637057642319261 := by
  unfold tailWord_4366408
  simp only [CollatzResearch.WordTrace]
  refine ⟨79627991582628506980729939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106170655443504675974306585 79627991582628506980729939)
  ·
    refine ⟨119441987373942760471094909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79627991582628506980729939 119441987373942760471094909)
    ·
      refine ⟨44790745265228535176660591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119441987373942760471094909 44790745265228535176660591)
      ·
        refine ⟨67186117897842802764990887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44790745265228535176660591 67186117897842802764990887)
        ·
          refine ⟨100779176846764204147486331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67186117897842802764990887 100779176846764204147486331)
          ·
            refine ⟨151168765270146306221229497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100779176846764204147486331 151168765270146306221229497)
            ·
              refine ⟨113376573952609729665922123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151168765270146306221229497 113376573952609729665922123)
              ·
                refine ⟨170064860928914594498883185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113376573952609729665922123 170064860928914594498883185)
                ·
                  refine ⟨127548645696685945874162389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170064860928914594498883185 127548645696685945874162389)
                  ·
                    refine ⟨2989421383516076856425681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127548645696685945874162389 2989421383516076856425681)
                    ·
                      refine ⟨2242066037637057642319261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989421383516076856425681 2242066037637057642319261)
                      ·
                        rfl

theorem cell23_4366408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_4366408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366408 prefixEnd_4366408 := by exact prefixLift 4366408
  have htrace : WordTrace (prefixWord ++ tailWord_4366408) baseStart_4366408 baseEnd_4366408 := by
    simpa [prefixWord, tailWord_4366408, baseEnd_4366408] using wordTrace_append hprefix tailTrace_4366408
  have hstable : (prefixWord ++ tailWord_4366408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366408).length < 2 ^ (prefixWord ++ tailWord_4366408).sum := by decide
  have hdescent : baseEnd_4366408 < baseStart_4366408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366422 : List Nat := [5, 2, 2, 1, 1, 1, 4, 7]
def baseStart_4366422 : Nat := 118140960795 + 4366422 * 2 ^ 59
def prefixEnd_4366422 : Nat := 4983230072969 + 3 ^ 40 * 4366422 * 2
def baseEnd_4366422 : Nat := 83039749124674836575711

theorem tailTrace_4366422 : CollatzResearch.WordTrace tailWord_4366422 prefixEnd_4366422 83039749124674836575711 := by
  unfold tailWord_4366422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953530861700393397029345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106170995858137529568313013 9953530861700393397029345)
  ·
    refine ⟨7465148146275295047772009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9953530861700393397029345 7465148146275295047772009)
    ·
      refine ⟨5598861109706471285829007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7465148146275295047772009 5598861109706471285829007)
      ·
        refine ⟨8398291664559706928743511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598861109706471285829007 8398291664559706928743511)
        ·
          refine ⟨12597437496839560393115267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398291664559706928743511 12597437496839560393115267)
          ·
            refine ⟨18896156245259340589672901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12597437496839560393115267 18896156245259340589672901)
            ·
              refine ⟨3543029295986126360563669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18896156245259340589672901 3543029295986126360563669)
              ·
                refine ⟨83039749124674836575711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3543029295986126360563669 83039749124674836575711)
                ·
                  rfl

theorem cell23_4366422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_4366422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366422 prefixEnd_4366422 := by exact prefixLift 4366422
  have htrace : WordTrace (prefixWord ++ tailWord_4366422) baseStart_4366422 baseEnd_4366422 := by
    simpa [prefixWord, tailWord_4366422, baseEnd_4366422] using wordTrace_append hprefix tailTrace_4366422
  have hstable : (prefixWord ++ tailWord_4366422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366422).length < 2 ^ (prefixWord ++ tailWord_4366422).sum := by decide
  have hdescent : baseEnd_4366422 < baseStart_4366422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366428 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4366428 : Nat := 118140960795 + 4366428 * 2 ^ 59
def prefixEnd_4366428 : Nat := 4983230072969 + 3 ^ 40 * 4366428 * 2
def baseEnd_4366428 : Nat := 2242076307250147564069169

theorem tailTrace_4366428 : CollatzResearch.WordTrace tailWord_4366428 prefixEnd_4366428 2242076307250147564069169 := by
  unfold tailWord_4366428
  simp only [CollatzResearch.WordTrace]
  refine ⟨79628356312592278688593969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106171141750123038251458625 79628356312592278688593969)
  ·
    refine ⟨59721267234444209016445477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79628356312592278688593969 59721267234444209016445477)
    ·
      refine ⟨11197737606458289190583527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59721267234444209016445477 11197737606458289190583527)
      ·
        refine ⟨16796606409687433785875291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11197737606458289190583527 16796606409687433785875291)
        ·
          refine ⟨25194909614531150678812937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16796606409687433785875291 25194909614531150678812937)
          ·
            refine ⟨18896182210898363009109703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25194909614531150678812937 18896182210898363009109703)
            ·
              refine ⟨28344273316347544513664555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18896182210898363009109703 28344273316347544513664555)
              ·
                refine ⟨42516409974521316770496833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28344273316347544513664555 42516409974521316770496833)
                ·
                  refine ⟨31887307480890987577872625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42516409974521316770496833 31887307480890987577872625)
                  ·
                    refine ⟨23915480610668240683404469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31887307480890987577872625 23915480610668240683404469)
                    ·
                      refine ⟨2242076307250147564069169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23915480610668240683404469 2242076307250147564069169)
                      ·
                        rfl

theorem cell23_4366428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4366428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366428 prefixEnd_4366428 := by exact prefixLift 4366428
  have htrace : WordTrace (prefixWord ++ tailWord_4366428) baseStart_4366428 baseEnd_4366428 := by
    simpa [prefixWord, tailWord_4366428, baseEnd_4366428] using wordTrace_append hprefix tailTrace_4366428
  have hstable : (prefixWord ++ tailWord_4366428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366428).length < 2 ^ (prefixWord ++ tailWord_4366428).sum := by decide
  have hdescent : baseEnd_4366428 < baseStart_4366428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366431 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 4, 6]
def baseStart_4366431 : Nat := 118140960795 + 4366431 * 2 ^ 59
def prefixEnd_4366431 : Nat := 4983230072969 + 3 ^ 40 * 4366431 * 2
def baseEnd_4366431 : Nat := 747359282564037017443885

theorem tailTrace_4366431 : CollatzResearch.WordTrace tailWord_4366431 prefixEnd_4366431 747359282564037017443885 := by
  unfold tailWord_4366431
  simp only [CollatzResearch.WordTrace]
  refine ⟨159256822044173688889547147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106171214696115792593031431 159256822044173688889547147)
  ·
    refine ⟨238885233066260533334320721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159256822044173688889547147 238885233066260533334320721)
    ·
      refine ⟨179163924799695400000740541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238885233066260533334320721 179163924799695400000740541)
      ·
        refine ⟨67186471799885775000277703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179163924799695400000740541 67186471799885775000277703)
        ·
          refine ⟨100779707699828662500416555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67186471799885775000277703 100779707699828662500416555)
          ·
            refine ⟨151169561549742993750624833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100779707699828662500416555 151169561549742993750624833)
            ·
              refine ⟨113377171162307245312968625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151169561549742993750624833 113377171162307245312968625)
              ·
                refine ⟨85032878371730433984726469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113377171162307245312968625 85032878371730433984726469)
                ·
                  refine ⟨15943664694699456372136213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85032878371730433984726469 15943664694699456372136213)
                  ·
                    refine ⟨747359282564037017443885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15943664694699456372136213 747359282564037017443885)
                    ·
                      rfl

theorem cell23_4366431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_4366431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366431 prefixEnd_4366431 := by exact prefixLift 4366431
  have htrace : WordTrace (prefixWord ++ tailWord_4366431) baseStart_4366431 baseEnd_4366431 := by
    simpa [prefixWord, tailWord_4366431, baseEnd_4366431] using wordTrace_append hprefix tailTrace_4366431
  have hstable : (prefixWord ++ tailWord_4366431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366431).length < 2 ^ (prefixWord ++ tailWord_4366431).sum := by decide
  have hdescent : baseEnd_4366431 < baseStart_4366431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366468 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4366468 : Nat := 118140960795 + 4366468 * 2 ^ 59
def prefixEnd_4366468 : Nat := 4983230072969 + 3 ^ 40 * 4366468 * 2
def baseEnd_4366468 : Nat := 2242096846476327407568985

theorem tailTrace_4366468 : CollatzResearch.WordTrace tailWord_4366468 prefixEnd_4366468 2242096846476327407568985 := by
  unfold tailWord_4366468
  simp only [CollatzResearch.WordTrace]
  refine ⟨79629085772519822104322029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106172114363359762805762705 79629085772519822104322029)
  ·
    refine ⟨29860907164694933289120761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79629085772519822104322029 29860907164694933289120761)
    ·
      refine ⟨22395680373521199966840571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29860907164694933289120761 22395680373521199966840571)
      ·
        refine ⟨33593520560281799950260857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22395680373521199966840571 33593520560281799950260857)
        ·
          refine ⟨25195140420211349962695643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33593520560281799950260857 25195140420211349962695643)
          ·
            refine ⟨37792710630317024944043465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25195140420211349962695643 37792710630317024944043465)
            ·
              refine ⟨28344532972737768708032599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37792710630317024944043465 28344532972737768708032599)
              ·
                refine ⟨42516799459106653062048899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28344532972737768708032599 42516799459106653062048899)
                ·
                  refine ⟨63775199188659979593073349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42516799459106653062048899 63775199188659979593073349)
                  ·
                    refine ⟨11957849847873746173701253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63775199188659979593073349 11957849847873746173701253)
                    ·
                      refine ⟨2242096846476327407568985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11957849847873746173701253 2242096846476327407568985)
                      ·
                        rfl

theorem cell23_4366468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4366468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366468 prefixEnd_4366468 := by exact prefixLift 4366468
  have htrace : WordTrace (prefixWord ++ tailWord_4366468) baseStart_4366468 baseEnd_4366468 := by
    simpa [prefixWord, tailWord_4366468, baseEnd_4366468] using wordTrace_append hprefix tailTrace_4366468
  have hstable : (prefixWord ++ tailWord_4366468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366468).length < 2 ^ (prefixWord ++ tailWord_4366468).sum := by decide
  have hdescent : baseEnd_4366468 < baseStart_4366468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366481 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_4366481 : Nat := 118140960795 + 4366481 * 2 ^ 59
def prefixEnd_4366481 : Nat := 4983230072969 + 3 ^ 40 * 4366481 * 2
def baseEnd_4366481 : Nat := 2242103521724835856706425

theorem tailTrace_4366481 : CollatzResearch.WordTrace tailWord_4366481 prefixEnd_4366481 2242103521724835856706425 := by
  unfold tailWord_4366481
  simp only [CollatzResearch.WordTrace]
  refine ⟨159258645693992547428867297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106172430462661698285911531 159258645693992547428867297)
  ·
    refine ⟨119443984270494410571650473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159258645693992547428867297 119443984270494410571650473)
    ·
      refine ⟨89582988202870807928737855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119443984270494410571650473 89582988202870807928737855)
      ·
        refine ⟨134374482304306211893106783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89582988202870807928737855 134374482304306211893106783)
        ·
          refine ⟨201561723456459317839660175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134374482304306211893106783 201561723456459317839660175)
          ·
            refine ⟨302342585184688976759490263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201561723456459317839660175 302342585184688976759490263)
            ·
              refine ⟨453513877777033465139235395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302342585184688976759490263 453513877777033465139235395)
              ·
                refine ⟨680270816665550197708853093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453513877777033465139235395 680270816665550197708853093)
                ·
                  refine ⟨127550778124790662070409955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680270816665550197708853093 127550778124790662070409955)
                  ·
                    refine ⟨191326167187185993105614933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127550778124790662070409955 191326167187185993105614933)
                    ·
                      refine ⟨2242103521724835856706425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191326167187185993105614933 2242103521724835856706425)
                      ·
                        rfl

theorem cell23_4366481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_4366481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366481 prefixEnd_4366481 := by exact prefixLift 4366481
  have htrace : WordTrace (prefixWord ++ tailWord_4366481) baseStart_4366481 baseEnd_4366481 := by
    simpa [prefixWord, tailWord_4366481, baseEnd_4366481] using wordTrace_append hprefix tailTrace_4366481
  have hstable : (prefixWord ++ tailWord_4366481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366481).length < 2 ^ (prefixWord ++ tailWord_4366481).sum := by decide
  have hdescent : baseEnd_4366481 < baseStart_4366481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366542 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_4366542 : Nat := 118140960795 + 4366542 * 2 ^ 59
def prefixEnd_4366542 : Nat := 4983230072969 + 3 ^ 40 * 4366542 * 2
def baseEnd_4366542 : Nat := 747378281348253372681215

theorem tailTrace_4366542 : CollatzResearch.WordTrace tailWord_4366542 prefixEnd_4366542 747378281348253372681215 := by
  unfold tailWord_4366542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19907608818346444355854735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106173913697847703231225253 19907608818346444355854735)
  ·
    refine ⟨29861413227519666533782103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19907608818346444355854735 29861413227519666533782103)
    ·
      refine ⟨44792119841279499800673155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29861413227519666533782103 44792119841279499800673155)
      ·
        refine ⟨67188179761919249701009733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44792119841279499800673155 67188179761919249701009733)
        ·
          refine ⟨12597783705359859318939325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67188179761919249701009733 12597783705359859318939325)
          ·
            refine ⟨4724168889509947244602247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12597783705359859318939325 4724168889509947244602247)
            ·
              refine ⟨7086253334264920866903371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724168889509947244602247 7086253334264920866903371)
              ·
                refine ⟨10629380001397381300355057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086253334264920866903371 10629380001397381300355057)
                ·
                  refine ⟨7972035001048035975266293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10629380001397381300355057 7972035001048035975266293)
                  ·
                    refine ⟨747378281348253372681215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7972035001048035975266293 747378281348253372681215)
                    ·
                      rfl

theorem cell23_4366542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_4366542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366542 prefixEnd_4366542 := by exact prefixLift 4366542
  have htrace : WordTrace (prefixWord ++ tailWord_4366542) baseStart_4366542 baseEnd_4366542 := by
    simpa [prefixWord, tailWord_4366542, baseEnd_4366542] using wordTrace_append hprefix tailTrace_4366542
  have hstable : (prefixWord ++ tailWord_4366542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366542).length < 2 ^ (prefixWord ++ tailWord_4366542).sum := by decide
  have hdescent : baseEnd_4366542 < baseStart_4366542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366545 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_4366545 : Nat := 118140960795 + 4366545 * 2 ^ 59
def prefixEnd_4366545 : Nat := 4983230072969 + 3 ^ 40 * 4366545 * 2
def baseEnd_4366545 : Nat := 2242136384486723606306131

theorem tailTrace_4366545 : CollatzResearch.WordTrace tailWord_4366545 prefixEnd_4366545 2242136384486723606306131 := by
  unfold tailWord_4366545
  simp only [CollatzResearch.WordTrace]
  refine ⟨159260979965760686359197089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106173986643840457572798059 159260979965760686359197089)
  ·
    refine ⟨119445734974320514769397817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159260979965760686359197089 119445734974320514769397817)
    ·
      refine ⟨89584301230740386077048363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119445734974320514769397817 89584301230740386077048363)
      ·
        refine ⟨134376451846110579115572545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89584301230740386077048363 134376451846110579115572545)
        ·
          refine ⟨100782338884582934336679409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134376451846110579115572545 100782338884582934336679409)
          ·
            refine ⟨75586754163437200752509557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100782338884582934336679409 75586754163437200752509557)
            ·
              refine ⟨7086258202822237570547771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75586754163437200752509557 7086258202822237570547771)
              ·
                refine ⟨10629387304233356355821657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086258202822237570547771 10629387304233356355821657)
                ·
                  refine ⟨7972040478175017266866243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10629387304233356355821657 7972040478175017266866243)
                  ·
                    refine ⟨11958060717262525900299365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7972040478175017266866243 11958060717262525900299365)
                    ·
                      refine ⟨2242136384486723606306131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11958060717262525900299365 2242136384486723606306131)
                      ·
                        rfl

theorem cell23_4366545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_4366545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366545 prefixEnd_4366545 := by exact prefixLift 4366545
  have htrace : WordTrace (prefixWord ++ tailWord_4366545) baseStart_4366545 baseEnd_4366545 := by
    simpa [prefixWord, tailWord_4366545, baseEnd_4366545] using wordTrace_append hprefix tailTrace_4366545
  have hstable : (prefixWord ++ tailWord_4366545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366545).length < 2 ^ (prefixWord ++ tailWord_4366545).sum := by decide
  have hdescent : baseEnd_4366545 < baseStart_4366545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366572 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_4366572 : Nat := 118140960795 + 4366572 * 2 ^ 59
def prefixEnd_4366572 : Nat := 4983230072969 + 3 ^ 40 * 4366572 * 2
def baseEnd_4366572 : Nat := 747383416154798333556169

theorem tailTrace_4366572 : CollatzResearch.WordTrace tailWord_4366572 prefixEnd_4366572 747383416154798333556169 := by
  unfold tailWord_4366572
  simp only [CollatzResearch.WordTrace]
  refine ⟨79630982368331434985214985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106174643157775246646953313 79630982368331434985214985)
  ·
    refine ⟨59723236776248576238911239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79630982368331434985214985 59723236776248576238911239)
    ·
      refine ⟨89584855164372864358366859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59723236776248576238911239 89584855164372864358366859)
      ·
        refine ⟨134377282746559296537550289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89584855164372864358366859 134377282746559296537550289)
        ·
          refine ⟨100782962059919472403162717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134377282746559296537550289 100782962059919472403162717)
          ·
            refine ⟨37793610772469802151186019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100782962059919472403162717 37793610772469802151186019)
            ·
              refine ⟨56690416158704703226779029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37793610772469802151186019 56690416158704703226779029)
              ·
                refine ⟨2657363257439282963755267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56690416158704703226779029 2657363257439282963755267)
                ·
                  refine ⟨3986044886158924445632901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657363257439282963755267 3986044886158924445632901)
                  ·
                    refine ⟨747383416154798333556169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986044886158924445632901 747383416154798333556169)
                    ·
                      rfl

theorem cell23_4366572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_4366572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366572 prefixEnd_4366572 := by exact prefixLift 4366572
  have htrace : WordTrace (prefixWord ++ tailWord_4366572) baseStart_4366572 baseEnd_4366572 := by
    simpa [prefixWord, tailWord_4366572, baseEnd_4366572] using wordTrace_append hprefix tailTrace_4366572
  have hstable : (prefixWord ++ tailWord_4366572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366572).length < 2 ^ (prefixWord ++ tailWord_4366572).sum := by decide
  have hdescent : baseEnd_4366572 < baseStart_4366572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366645 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4366645 : Nat := 118140960795 + 4366645 * 2 ^ 59
def prefixEnd_4366645 : Nat := 4983230072969 + 3 ^ 40 * 4366645 * 2
def baseEnd_4366645 : Nat := 747395910850724405018557

theorem tailTrace_4366645 : CollatzResearch.WordTrace tailWord_4366645 prefixEnd_4366645 747395910850724405018557 := by
  unfold tailWord_4366645
  simp only [CollatzResearch.WordTrace]
  refine ⟨159264627265398403437837389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106176418176932268958558259 159264627265398403437837389)
  ·
    refine ⟨59724235224524401289189021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159264627265398403437837389 59724235224524401289189021)
    ·
      refine ⟨22396588209196650483445883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59724235224524401289189021 22396588209196650483445883)
      ·
        refine ⟨33594882313794975725168825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22396588209196650483445883 33594882313794975725168825)
        ·
          refine ⟨25196161735346231793876619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33594882313794975725168825 25196161735346231793876619)
          ·
            refine ⟨37794242603019347690814929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25196161735346231793876619 37794242603019347690814929)
            ·
              refine ⟨28345681952264510768111197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37794242603019347690814929 28345681952264510768111197)
              ·
                refine ⟨10629630732099191538041699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28345681952264510768111197 10629630732099191538041699)
                ·
                  refine ⟨15944446098148787307062549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10629630732099191538041699 15944446098148787307062549)
                  ·
                    refine ⟨747395910850724405018557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15944446098148787307062549 747395910850724405018557)
                    ·
                      rfl

theorem cell23_4366645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4366645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366645 prefixEnd_4366645 := by exact prefixLift 4366645
  have htrace : WordTrace (prefixWord ++ tailWord_4366645) baseStart_4366645 baseEnd_4366645 := by
    simpa [prefixWord, tailWord_4366645, baseEnd_4366645] using wordTrace_append hprefix tailTrace_4366645
  have hstable : (prefixWord ++ tailWord_4366645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366645).length < 2 ^ (prefixWord ++ tailWord_4366645).sum := by decide
  have hdescent : baseEnd_4366645 < baseStart_4366645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366649 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_4366649 : Nat := 118140960795 + 4366649 * 2 ^ 59
def prefixEnd_4366649 : Nat := 4983230072969 + 3 ^ 40 * 4366649 * 2
def baseEnd_4366649 : Nat := 747396595491597066468551

theorem tailTrace_4366649 : CollatzResearch.WordTrace tailWord_4366649 prefixEnd_4366649 747396595491597066468551 := by
  unfold tailWord_4366649
  simp only [CollatzResearch.WordTrace]
  refine ⟨159264773157383912120983001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106176515438255941413988667 159264773157383912120983001)
  ·
    refine ⟨119448579868037934090737251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159264773157383912120983001 119448579868037934090737251)
    ·
      refine ⟨179172869802056901136105877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119448579868037934090737251 179172869802056901136105877)
      ·
        refine ⟨8398728271971417240754963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179172869802056901136105877 8398728271971417240754963)
        ·
          refine ⟨12598092407957125861132445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398728271971417240754963 12598092407957125861132445)
          ·
            refine ⟨4724284652983922197924667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12598092407957125861132445 4724284652983922197924667)
            ·
              refine ⟨7086426979475883296887001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724284652983922197924667 7086426979475883296887001)
              ·
                refine ⟨5314820234606912472665251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7086426979475883296887001 5314820234606912472665251)
                ·
                  refine ⟨7972230351910368708997877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314820234606912472665251 7972230351910368708997877)
                  ·
                    refine ⟨747396595491597066468551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7972230351910368708997877 747396595491597066468551)
                    ·
                      rfl

theorem cell23_4366649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_4366649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366649 prefixEnd_4366649 := by exact prefixLift 4366649
  have htrace : WordTrace (prefixWord ++ tailWord_4366649) baseStart_4366649 baseEnd_4366649 := by
    simpa [prefixWord, tailWord_4366649, baseEnd_4366649] using wordTrace_append hprefix tailTrace_4366649
  have hstable : (prefixWord ++ tailWord_4366649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366649).length < 2 ^ (prefixWord ++ tailWord_4366649).sum := by decide
  have hdescent : baseEnd_4366649 < baseStart_4366649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366672 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_4366672 : Nat := 118140960795 + 4366672 * 2 ^ 59
def prefixEnd_4366672 : Nat := 4983230072969 + 3 ^ 40 * 4366672 * 2
def baseEnd_4366672 : Nat := 2242201596529844609418047

theorem tailTrace_4366672 : CollatzResearch.WordTrace tailWord_4366672 prefixEnd_4366672 2242201596529844609418047 := by
  unfold tailWord_4366672
  simp only [CollatzResearch.WordTrace]
  refine ⟨79632806018150293524535135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106177074690867058032713513 79632806018150293524535135)
  ·
    refine ⟨119449209027225440286802703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79632806018150293524535135 119449209027225440286802703)
    ·
      refine ⟨179173813540838160430204055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119449209027225440286802703 179173813540838160430204055)
      ·
        refine ⟨268760720311257240645306083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179173813540838160430204055 268760720311257240645306083)
        ·
          refine ⟨403141080466885860967959125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268760720311257240645306083 403141080466885860967959125)
          ·
            refine ⟨4724309536721318683218271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 403141080466885860967959125 4724309536721318683218271)
            ·
              refine ⟨7086464305081978024827407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724309536721318683218271 7086464305081978024827407)
              ·
                refine ⟨10629696457622967037241111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086464305081978024827407 10629696457622967037241111)
                ·
                  refine ⟨15944544686434450555861667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10629696457622967037241111 15944544686434450555861667)
                  ·
                    refine ⟨23916817029651675833792501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15944544686434450555861667 23916817029651675833792501)
                    ·
                      refine ⟨2242201596529844609418047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23916817029651675833792501 2242201596529844609418047)
                      ·
                        rfl

theorem cell23_4366672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_4366672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366672 prefixEnd_4366672 := by exact prefixLift 4366672
  have htrace : WordTrace (prefixWord ++ tailWord_4366672) baseStart_4366672 baseEnd_4366672 := by
    simpa [prefixWord, tailWord_4366672, baseEnd_4366672] using wordTrace_append hprefix tailTrace_4366672
  have hstable : (prefixWord ++ tailWord_4366672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366672).length < 2 ^ (prefixWord ++ tailWord_4366672).sum := by decide
  have hdescent : baseEnd_4366672 < baseStart_4366672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366723 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 1, 2, 3]
def baseStart_4366723 : Nat := 118140960795 + 4366723 * 2 ^ 59
def prefixEnd_4366723 : Nat := 4983230072969 + 3 ^ 40 * 4366723 * 2
def baseEnd_4366723 : Nat := 2242227784043223909880313

theorem tailTrace_4366723 : CollatzResearch.WordTrace tailWord_4366723 prefixEnd_4366723 2242227784043223909880313 := by
  unfold tailWord_4366723
  simp only [CollatzResearch.WordTrace]
  refine ⟨159267472159115822759176823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106178314772743881839451215 159267472159115822759176823)
  ·
    refine ⟨238901208238673734138765235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159267472159115822759176823 238901208238673734138765235)
    ·
      refine ⟨358351812358010601208147853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238901208238673734138765235 358351812358010601208147853)
      ·
        refine ⟨134381929634253975453055445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358351812358010601208147853 134381929634253975453055445)
        ·
          refine ⟨3149576475802827549680987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 134381929634253975453055445 3149576475802827549680987)
          ·
            refine ⟨4724364713704241324521481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149576475802827549680987 4724364713704241324521481)
            ·
              refine ⟨3543273535278180993391111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4724364713704241324521481 3543273535278180993391111)
              ·
                refine ⟨5314910302917271490086667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543273535278180993391111 5314910302917271490086667)
                ·
                  refine ⟨7972365454375907235130001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314910302917271490086667 7972365454375907235130001)
                  ·
                    refine ⟨5979274090781930426347501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7972365454375907235130001 5979274090781930426347501)
                    ·
                      refine ⟨2242227784043223909880313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5979274090781930426347501 2242227784043223909880313)
                      ·
                        rfl

theorem cell23_4366723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_4366723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366723 prefixEnd_4366723 := by exact prefixLift 4366723
  have htrace : WordTrace (prefixWord ++ tailWord_4366723) baseStart_4366723 baseEnd_4366723 := by
    simpa [prefixWord, tailWord_4366723, baseEnd_4366723] using wordTrace_append hprefix tailTrace_4366723
  have hstable : (prefixWord ++ tailWord_4366723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366723).length < 2 ^ (prefixWord ++ tailWord_4366723).sum := by decide
  have hdescent : baseEnd_4366723 < baseStart_4366723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366753 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4366753 : Nat := 118140960795 + 4366753 * 2 ^ 59
def prefixEnd_4366753 : Nat := 4983230072969 + 3 ^ 40 * 4366753 * 2
def baseEnd_4366753 : Nat := 2242243188462858792505175

theorem tailTrace_4366753 : CollatzResearch.WordTrace tailWord_4366753 prefixEnd_4366753 2242243188462858792505175 := by
  unfold tailWord_4366753
  simp only [CollatzResearch.WordTrace]
  refine ⟨159268566349007137882768913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106179044232671425255179275 159268566349007137882768913)
  ·
    refine ⟨119451424761755353412076685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159268566349007137882768913 119451424761755353412076685)
    ·
      refine ⟨44794284285658257529528757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119451424761755353412076685 44794284285658257529528757)
      ·
        refine ⟨4199464151780461643393321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44794284285658257529528757 4199464151780461643393321)
        ·
          refine ⟨3149598113835346232544991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199464151780461643393321 3149598113835346232544991)
          ·
            refine ⟨4724397170753019348817487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149598113835346232544991 4724397170753019348817487)
            ·
              refine ⟨7086595756129529023226231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724397170753019348817487 7086595756129529023226231)
              ·
                refine ⟨10629893634194293534839347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086595756129529023226231 10629893634194293534839347)
                ·
                  refine ⟨15944840451291440302259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10629893634194293534839347 15944840451291440302259021)
                  ·
                    refine ⟨5979315169234290113347133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15944840451291440302259021 5979315169234290113347133)
                    ·
                      refine ⟨2242243188462858792505175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5979315169234290113347133 2242243188462858792505175)
                      ·
                        rfl

theorem cell23_4366753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4366753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366753 prefixEnd_4366753 := by exact prefixLift 4366753
  have htrace : WordTrace (prefixWord ++ tailWord_4366753) baseStart_4366753 baseEnd_4366753 := by
    simpa [prefixWord, tailWord_4366753, baseEnd_4366753] using wordTrace_append hprefix tailTrace_4366753
  have hstable : (prefixWord ++ tailWord_4366753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366753).length < 2 ^ (prefixWord ++ tailWord_4366753).sum := by decide
  have hdescent : baseEnd_4366753 < baseStart_4366753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366829 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_4366829 : Nat := 118140960795 + 4366829 * 2 ^ 59
def prefixEnd_4366829 : Nat := 4983230072969 + 3 ^ 40 * 4366829 * 2
def baseEnd_4366829 : Nat := 747427404330866831718275

theorem tailTrace_4366829 : CollatzResearch.WordTrace tailWord_4366829 prefixEnd_4366829 747427404330866831718275 := by
  unfold tailWord_4366829
  simp only [CollatzResearch.WordTrace]
  refine ⟨159271338296731802862535541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106180892197821201908357027 159271338296731802862535541)
  ·
    refine ⟨14931687965318606518362707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159271338296731802862535541 14931687965318606518362707)
    ·
      refine ⟨22397531947977909777544061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14931687965318606518362707 22397531947977909777544061)
      ·
        refine ⟨8399074480491716166579023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22397531947977909777544061 8399074480491716166579023)
        ·
          refine ⟨12598611720737574249868535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399074480491716166579023 12598611720737574249868535)
          ·
            refine ⟨18897917581106361374802803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598611720737574249868535 18897917581106361374802803)
            ·
              refine ⟨28346876371659542062204205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18897917581106361374802803 28346876371659542062204205)
              ·
                refine ⟨10630078639372328273326577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28346876371659542062204205 10630078639372328273326577)
                ·
                  refine ⟨7972558979529246204994933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10630078639372328273326577 7972558979529246204994933)
                  ·
                    refine ⟨747427404330866831718275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7972558979529246204994933 747427404330866831718275)
                    ·
                      rfl

theorem cell23_4366829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_4366829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366829 prefixEnd_4366829 := by exact prefixLift 4366829
  have htrace : WordTrace (prefixWord ++ tailWord_4366829) baseStart_4366829 baseEnd_4366829 := by
    simpa [prefixWord, tailWord_4366829, baseEnd_4366829] using wordTrace_append hprefix tailTrace_4366829
  have hstable : (prefixWord ++ tailWord_4366829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366829).length < 2 ^ (prefixWord ++ tailWord_4366829).sum := by decide
  have hdescent : baseEnd_4366829 < baseStart_4366829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366842 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_4366842 : Nat := 118140960795 + 4366842 * 2 ^ 59
def prefixEnd_4366842 : Nat := 4983230072969 + 3 ^ 40 * 4366842 * 2
def baseEnd_4366842 : Nat := 747429629413702981430755

theorem tailTrace_4366842 : CollatzResearch.WordTrace tailWord_4366842 prefixEnd_4366842 747429629413702981430755 := by
  unfold tailWord_4366842
  simp only [CollatzResearch.WordTrace]
  refine ⟨39817953111421176520689695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106181208297123137388505853 39817953111421176520689695)
  ·
    refine ⟨59726929667131764781034543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39817953111421176520689695 59726929667131764781034543)
    ·
      refine ⟨89590394500697647171551815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59726929667131764781034543 89590394500697647171551815)
      ·
        refine ⟨134385591751046470757327723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89590394500697647171551815 134385591751046470757327723)
        ·
          refine ⟨201578387626569706135991585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134385591751046470757327723 201578387626569706135991585)
          ·
            refine ⟨151183790719927279601993689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201578387626569706135991585 151183790719927279601993689)
            ·
              refine ⟨113387843039945459701495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151183790719927279601993689 113387843039945459701495267)
              ·
                refine ⟨170081764559918189552242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113387843039945459701495267 170081764559918189552242901)
                ·
                  refine ⟨3986291356873082567630693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170081764559918189552242901 3986291356873082567630693)
                  ·
                    refine ⟨747429629413702981430755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986291356873082567630693 747429629413702981430755)
                    ·
                      rfl

theorem cell23_4366842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_4366842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366842 prefixEnd_4366842 := by exact prefixLift 4366842
  have htrace : WordTrace (prefixWord ++ tailWord_4366842) baseStart_4366842 baseEnd_4366842 := by
    simpa [prefixWord, tailWord_4366842, baseEnd_4366842] using wordTrace_append hprefix tailTrace_4366842
  have hstable : (prefixWord ++ tailWord_4366842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366842).length < 2 ^ (prefixWord ++ tailWord_4366842).sum := by decide
  have hdescent : baseEnd_4366842 < baseStart_4366842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366849 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4366849 : Nat := 118140960795 + 4366849 * 2 ^ 59
def prefixEnd_4366849 : Nat := 4983230072969 + 3 ^ 40 * 4366849 * 2
def baseEnd_4366849 : Nat := 2242292482605690416904733

theorem tailTrace_4366849 : CollatzResearch.WordTrace tailWord_4366849 prefixEnd_4366849 2242292482605690416904733 := by
  unfold tailWord_4366849
  simp only [CollatzResearch.WordTrace]
  refine ⟨159272067756659346278263601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106181378504439564185509067 159272067756659346278263601)
  ·
    refine ⟨119454050817494509708697701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159272067756659346278263601 119454050817494509708697701)
    ·
      refine ⟨22397634528280220570380819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119454050817494509708697701 22397634528280220570380819)
      ·
        refine ⟨33596451792420330855571229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22397634528280220570380819 33596451792420330855571229)
        ·
          refine ⟨12598669422157624070839211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33596451792420330855571229 12598669422157624070839211)
          ·
            refine ⟨18898004133236436106258817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598669422157624070839211 18898004133236436106258817)
            ·
              refine ⟨14173503099927327079694113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18898004133236436106258817 14173503099927327079694113)
              ·
                refine ⟨10630127324945495309770585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14173503099927327079694113 10630127324945495309770585)
                ·
                  refine ⟨7972595493709121482327939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10630127324945495309770585 7972595493709121482327939)
                  ·
                    refine ⟨11958893240563682223491909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7972595493709121482327939 11958893240563682223491909)
                    ·
                      refine ⟨2242292482605690416904733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11958893240563682223491909 2242292482605690416904733)
                      ·
                        rfl

theorem cell23_4366849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4366849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366849 prefixEnd_4366849 := by exact prefixLift 4366849
  have htrace : WordTrace (prefixWord ++ tailWord_4366849) baseStart_4366849 baseEnd_4366849 := by
    simpa [prefixWord, tailWord_4366849, baseEnd_4366849] using wordTrace_append hprefix tailTrace_4366849
  have hstable : (prefixWord ++ tailWord_4366849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366849).length < 2 ^ (prefixWord ++ tailWord_4366849).sum := by decide
  have hdescent : baseEnd_4366849 < baseStart_4366849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366850 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_4366850 : Nat := 118140960795 + 4366850 * 2 ^ 59
def prefixEnd_4366850 : Nat := 4983230072969 + 3 ^ 40 * 4366850 * 2
def baseEnd_4366850 : Nat := 249143666231816101443581

theorem tailTrace_4366850 : CollatzResearch.WordTrace tailWord_4366850 prefixEnd_4366850 249143666231816101443581 := by
  unfold tailWord_4366850
  simp only [CollatzResearch.WordTrace]
  refine ⟨39818026057413930862262501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106181402819770482299366669 39818026057413930862262501)
  ·
    refine ⟨7465879885765112036674219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39818026057413930862262501 7465879885765112036674219)
    ·
      refine ⟨11198819828647668055011329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465879885765112036674219 11198819828647668055011329)
      ·
        refine ⟨8399114871485751041258497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11198819828647668055011329 8399114871485751041258497)
        ·
          refine ⟨6299336153614313280943873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8399114871485751041258497 6299336153614313280943873)
          ·
            refine ⟨4724502115210734960707905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6299336153614313280943873 4724502115210734960707905)
            ·
              refine ⟨3543376586408051220530929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4724502115210734960707905 3543376586408051220530929)
              ·
                refine ⟨2657532439806038415398197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3543376586408051220530929 2657532439806038415398197)
                ·
                  refine ⟨249143666231816101443581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2657532439806038415398197 249143666231816101443581)
                  ·
                    rfl

theorem cell23_4366850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_4366850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366850 prefixEnd_4366850 := by exact prefixLift 4366850
  have htrace : WordTrace (prefixWord ++ tailWord_4366850) baseStart_4366850 baseEnd_4366850 := by
    simpa [prefixWord, tailWord_4366850, baseEnd_4366850] using wordTrace_append hprefix tailTrace_4366850
  have hstable : (prefixWord ++ tailWord_4366850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366850).length < 2 ^ (prefixWord ++ tailWord_4366850).sum := by decide
  have hdescent : baseEnd_4366850 < baseStart_4366850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366899 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 3]
def baseStart_4366899 : Nat := 118140960795 + 4366899 * 2 ^ 59
def prefixEnd_4366899 : Nat := 4983230072969 + 3 ^ 40 * 4366899 * 2
def baseEnd_4366899 : Nat := 2242318156638415221279503

theorem tailTrace_4366899 : CollatzResearch.WordTrace tailWord_4366899 prefixEnd_4366899 2242318156638415221279503 := by
  unfold tailWord_4366899
  simp only [CollatzResearch.WordTrace]
  refine ⟨159273891406478204817583751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106182594270985469878389167 159273891406478204817583751)
  ·
    refine ⟨238910837109717307226375627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159273891406478204817583751 238910837109717307226375627)
    ·
      refine ⟨358366255664575960839563441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238910837109717307226375627 358366255664575960839563441)
      ·
        refine ⟨268774691748431970629672581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358366255664575960839563441 268774691748431970629672581)
        ·
          refine ⟨50395254702830994493063609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268774691748431970629672581 50395254702830994493063609)
          ·
            refine ⟨37796441027123245869797707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50395254702830994493063609 37796441027123245869797707)
            ·
              refine ⟨56694661540684868804696561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37796441027123245869797707 56694661540684868804696561)
              ·
                refine ⟨42520996155513651603522421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56694661540684868804696561 42520996155513651603522421)
                ·
                  refine ⟨3986343389579404837830227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42520996155513651603522421 3986343389579404837830227)
                  ·
                    refine ⟨5979515084369107256745341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986343389579404837830227 5979515084369107256745341)
                    ·
                      refine ⟨2242318156638415221279503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5979515084369107256745341 2242318156638415221279503)
                      ·
                        rfl

theorem cell23_4366899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_4366899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366899 prefixEnd_4366899 := by exact prefixLift 4366899
  have htrace : WordTrace (prefixWord ++ tailWord_4366899) baseStart_4366899 baseEnd_4366899 := by
    simpa [prefixWord, tailWord_4366899, baseEnd_4366899] using wordTrace_append hprefix tailTrace_4366899
  have hstable : (prefixWord ++ tailWord_4366899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366899).length < 2 ^ (prefixWord ++ tailWord_4366899).sum := by decide
  have hdescent : baseEnd_4366899 < baseStart_4366899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4366956 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_4366956 : Nat := 118140960795 + 4366956 * 2 ^ 59
def prefixEnd_4366956 : Nat := 4983230072969 + 3 ^ 40 * 4366956 * 2
def baseEnd_4366956 : Nat := 2242347425035721498266741

theorem tailTrace_4366956 : CollatzResearch.WordTrace tailWord_4366956 prefixEnd_4366956 2242347425035721498266741 := by
  unfold tailWord_4366956
  simp only [CollatzResearch.WordTrace]
  refine ⟨79637985183635851776204361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106183980244847802368272481 79637985183635851776204361)
  ·
    refine ⟨59728488887726888832153271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79637985183635851776204361 59728488887726888832153271)
    ·
      refine ⟨89592733331590333248229907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59728488887726888832153271 89592733331590333248229907)
      ·
        refine ⟨134389099997385499872344861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89592733331590333248229907 134389099997385499872344861)
        ·
          refine ⟨50395912499019562452129323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134389099997385499872344861 50395912499019562452129323)
          ·
            refine ⟨75593868748529343678193985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50395912499019562452129323 75593868748529343678193985)
            ·
              refine ⟨56695401561397007758645489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75593868748529343678193985 56695401561397007758645489)
              ·
                refine ⟨42521551171047755818984117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56695401561397007758645489 42521551171047755818984117)
                ·
                  refine ⟨3986395422285727108029761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42521551171047755818984117 3986395422285727108029761)
                  ·
                    refine ⟨2989796566714295331022321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3986395422285727108029761 2989796566714295331022321)
                    ·
                      refine ⟨2242347425035721498266741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989796566714295331022321 2242347425035721498266741)
                      ·
                        rfl

theorem cell23_4366956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_4366956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4366956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4366956 prefixEnd_4366956 := by exact prefixLift 4366956
  have htrace : WordTrace (prefixWord ++ tailWord_4366956) baseStart_4366956 baseEnd_4366956 := by
    simpa [prefixWord, tailWord_4366956, baseEnd_4366956] using wordTrace_append hprefix tailTrace_4366956
  have hstable : (prefixWord ++ tailWord_4366956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4366956).length < 2 ^ (prefixWord ++ tailWord_4366956).sum := by decide
  have hdescent : baseEnd_4366956 < baseStart_4366956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4366956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367023 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 3]
def baseStart_4367023 : Nat := 118140960795 + 4367023 * 2 ^ 59
def prefixEnd_4367023 : Nat := 4983230072969 + 3 ^ 40 * 4367023 * 2
def baseEnd_4367023 : Nat := 2242381828239572736128933

theorem tailTrace_4367023 : CollatzResearch.WordTrace tailWord_4367023 prefixEnd_4367023 2242381828239572736128933 := by
  unfold tailWord_4367023
  simp only [CollatzResearch.WordTrace]
  refine ⟨159278414058028973995097723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106185609372019315996731815 159278414058028973995097723)
  ·
    refine ⟨238917621087043460992646585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159278414058028973995097723 238917621087043460992646585)
    ·
      refine ⟨179188215815282595744484939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238917621087043460992646585 179188215815282595744484939)
      ·
        refine ⟨268782323722923893616727409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179188215815282595744484939 268782323722923893616727409)
        ·
          refine ⟨201586742792192920212545557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268782323722923893616727409 201586742792192920212545557)
          ·
            refine ⟨9449378568384043134963073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 201586742792192920212545557 9449378568384043134963073)
            ·
              refine ⟨7087033926288032351222305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9449378568384043134963073 7087033926288032351222305)
              ·
                refine ⟨5315275444716024263416729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7087033926288032351222305 5315275444716024263416729)
                ·
                  refine ⟨3986456583537018197562547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5315275444716024263416729 3986456583537018197562547)
                  ·
                    refine ⟨5979684875305527296343821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986456583537018197562547 5979684875305527296343821)
                    ·
                      refine ⟨2242381828239572736128933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5979684875305527296343821 2242381828239572736128933)
                      ·
                        rfl

theorem cell23_4367023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_4367023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367023 prefixEnd_4367023 := by exact prefixLift 4367023
  have htrace : WordTrace (prefixWord ++ tailWord_4367023) baseStart_4367023 baseEnd_4367023 := by
    simpa [prefixWord, tailWord_4367023, baseEnd_4367023] using wordTrace_append hprefix tailTrace_4367023
  have hstable : (prefixWord ++ tailWord_4367023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367023).length < 2 ^ (prefixWord ++ tailWord_4367023).sum := by decide
  have hdescent : baseEnd_4367023 < baseStart_4367023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367030 : List Nat := [5, 1, 3, 1, 3, 1, 1, 8]
def baseStart_4367030 : Nat := 118140960795 + 4367030 * 2 ^ 59
def prefixEnd_4367030 : Nat := 4983230072969 + 3 ^ 40 * 4367030 * 2
def baseEnd_4367030 : Nat := 83051311948302007731163

theorem tailTrace_4367030 : CollatzResearch.WordTrace tailWord_4367030 prefixEnd_4367030 83051311948302007731163 := by
  unfold tailWord_4367030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954916835562725886912659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106185779579335742793735029 9954916835562725886912659)
  ·
    refine ⟨14932375253344088830368989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9954916835562725886912659 14932375253344088830368989)
    ·
      refine ⟨5599640720004033311388371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14932375253344088830368989 5599640720004033311388371)
      ·
        refine ⟨8399461080006049967082557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599640720004033311388371 8399461080006049967082557)
        ·
          refine ⟨3149797905002268737655959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8399461080006049967082557 3149797905002268737655959)
          ·
            refine ⟨4724696857503403106483939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149797905002268737655959 4724696857503403106483939)
            ·
              refine ⟨7087045286255104659725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724696857503403106483939 7087045286255104659725909)
              ·
                refine ⟨83051311948302007731163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7087045286255104659725909 83051311948302007731163)
                ·
                  rfl

theorem cell23_4367030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_4367030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367030 prefixEnd_4367030 := by exact prefixLift 4367030
  have htrace : WordTrace (prefixWord ++ tailWord_4367030) baseStart_4367030 baseEnd_4367030 := by
    simpa [prefixWord, tailWord_4367030, baseEnd_4367030] using wordTrace_append hprefix tailTrace_4367030
  have hstable : (prefixWord ++ tailWord_4367030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367030).length < 2 ^ (prefixWord ++ tailWord_4367030).sum := by decide
  have hdescent : baseEnd_4367030 < baseStart_4367030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367039 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 2, 6]
def baseStart_4367039 : Nat := 118140960795 + 4367039 * 2 ^ 59
def prefixEnd_4367039 : Nat := 4983230072969 + 3 ^ 40 * 4367039 * 2
def baseEnd_4367039 : Nat := 747463347976681557842953

theorem tailTrace_4367039 : CollatzResearch.WordTrace tailWord_4367039 prefixEnd_4367039 747463347976681557842953 := by
  unfold tailWord_4367039
  simp only [CollatzResearch.WordTrace]
  refine ⟨159278997625971008727680171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106185998417314005818453447 159278997625971008727680171)
  ·
    refine ⟨238918496438956513091520257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159278997625971008727680171 238918496438956513091520257)
    ·
      refine ⟨179188872329217384818640193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238918496438956513091520257 179188872329217384818640193)
      ·
        refine ⟨134391654246913038613980145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179188872329217384818640193 134391654246913038613980145)
        ·
          refine ⟨100793740685184778960485109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134391654246913038613980145 100793740685184778960485109)
          ·
            refine ⟨9449413189236073027545479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100793740685184778960485109 9449413189236073027545479)
            ·
              refine ⟨14174119783854109541318219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9449413189236073027545479 14174119783854109541318219)
              ·
                refine ⟨21261179675781164311977329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14174119783854109541318219 21261179675781164311977329)
                ·
                  refine ⟨15945884756835873233982997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21261179675781164311977329 15945884756835873233982997)
                  ·
                    refine ⟨747463347976681557842953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15945884756835873233982997 747463347976681557842953)
                    ·
                      rfl

theorem cell23_4367039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_4367039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367039 prefixEnd_4367039 := by exact prefixLift 4367039
  have htrace : WordTrace (prefixWord ++ tailWord_4367039) baseStart_4367039 baseEnd_4367039 := by
    simpa [prefixWord, tailWord_4367039, baseEnd_4367039] using wordTrace_append hprefix tailTrace_4367039
  have hstable : (prefixWord ++ tailWord_4367039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367039).length < 2 ^ (prefixWord ++ tailWord_4367039).sum := by decide
  have hdescent : baseEnd_4367039 < baseStart_4367039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367080 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_4367080 : Nat := 118140960795 + 4367080 * 2 ^ 59
def prefixEnd_4367080 : Nat := 4983230072969 + 3 ^ 40 * 4367080 * 2
def baseEnd_4367080 : Nat := 2242411096636879013116171

theorem tailTrace_4367080 : CollatzResearch.WordTrace tailWord_4367080 prefixEnd_4367080 2242411096636879013116171 := by
  unfold tailWord_4367080
  simp only [CollatzResearch.WordTrace]
  refine ⟨79640246509411236364961347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106186995345881648486615129 79640246509411236364961347)
  ·
    refine ⟨119460369764116854547442021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79640246509411236364961347 119460369764116854547442021)
    ·
      refine ⟨22398819330771910227645379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119460369764116854547442021 22398819330771910227645379)
      ·
        refine ⟨33598228996157865341468069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22398819330771910227645379 33598228996157865341468069)
        ·
          refine ⟨6299667936779599751525263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33598228996157865341468069 6299667936779599751525263)
          ·
            refine ⟨9449501905169399627287895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6299667936779599751525263 9449501905169399627287895)
            ·
              refine ⟨14174252857754099440931843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9449501905169399627287895 14174252857754099440931843)
              ·
                refine ⟨21261379286631149161397765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14174252857754099440931843 21261379286631149161397765)
                ·
                  refine ⟨3986508616243340467762081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21261379286631149161397765 3986508616243340467762081)
                  ·
                    refine ⟨2989881462182505350821561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3986508616243340467762081 2989881462182505350821561)
                    ·
                      refine ⟨2242411096636879013116171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989881462182505350821561 2242411096636879013116171)
                      ·
                        rfl

theorem cell23_4367080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_4367080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367080 prefixEnd_4367080 := by exact prefixLift 4367080
  have htrace : WordTrace (prefixWord ++ tailWord_4367080) baseStart_4367080 baseEnd_4367080 := by
    simpa [prefixWord, tailWord_4367080, baseEnd_4367080] using wordTrace_append hprefix tailTrace_4367080
  have hstable : (prefixWord ++ tailWord_4367080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367080).length < 2 ^ (prefixWord ++ tailWord_4367080).sum := by decide
  have hdescent : baseEnd_4367080 < baseStart_4367080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367086 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_4367086 : Nat := 118140960795 + 4367086 * 2 ^ 59
def prefixEnd_4367086 : Nat := 4983230072969 + 3 ^ 40 * 4367086 * 2
def baseEnd_4367086 : Nat := 249157130835645109960127

theorem tailTrace_4367086 : CollatzResearch.WordTrace tailWord_4367086 prefixEnd_4367086 249157130835645109960127 := by
  unfold tailWord_4367086
  simp only [CollatzResearch.WordTrace]
  refine ⟨19910088982100091969330139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106187141237867157169760741 19910088982100091969330139)
  ·
    refine ⟨29865133473150137953995209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19910088982100091969330139 29865133473150137953995209)
    ·
      refine ⟨22398850104862603465496407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29865133473150137953995209 22398850104862603465496407)
      ·
        refine ⟨33598275157293905198244611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22398850104862603465496407 33598275157293905198244611)
        ·
          refine ⟨50397412735940857797366917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33598275157293905198244611 50397412735940857797366917)
          ·
            refine ⟨9449514887988910837006297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50397412735940857797366917 9449514887988910837006297)
            ·
              refine ⟨7087136165991683127754723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9449514887988910837006297 7087136165991683127754723)
              ·
                refine ⟨10630704248987524691632085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7087136165991683127754723 10630704248987524691632085)
                ·
                  refine ⟨249157130835645109960127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10630704248987524691632085 249157130835645109960127)
                  ·
                    rfl

theorem cell23_4367086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_4367086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367086 prefixEnd_4367086 := by exact prefixLift 4367086
  have htrace : WordTrace (prefixWord ++ tailWord_4367086) baseStart_4367086 baseEnd_4367086 := by
    simpa [prefixWord, tailWord_4367086, baseEnd_4367086] using wordTrace_append hprefix tailTrace_4367086
  have hstable : (prefixWord ++ tailWord_4367086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367086).length < 2 ^ (prefixWord ++ tailWord_4367086).sum := by decide
  have hdescent : baseEnd_4367086 < baseStart_4367086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367119 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_4367119 : Nat := 118140960795 + 4367119 * 2 ^ 59
def prefixEnd_4367119 : Nat := 4983230072969 + 3 ^ 40 * 4367119 * 2
def baseEnd_4367119 : Nat := 2242431122382404360528491

theorem tailTrace_4367119 : CollatzResearch.WordTrace tailWord_4367119 prefixEnd_4367119 2242431122382404360528491 := by
  unfold tailWord_4367119
  simp only [CollatzResearch.WordTrace]
  refine ⟨159281915465681182390592411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106187943643787454927061607 159281915465681182390592411)
  ·
    refine ⟨238922873198521773585888617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159281915465681182390592411 238922873198521773585888617)
    ·
      refine ⟨179192154898891330189416463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238922873198521773585888617 179192154898891330189416463)
      ·
        refine ⟨268788232348336995284124695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179192154898891330189416463 268788232348336995284124695)
        ·
          refine ⟨403182348522505492926187043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268788232348336995284124695 403182348522505492926187043)
          ·
            refine ⟨604773522783758239389280565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403182348522505492926187043 604773522783758239389280565)
            ·
              refine ⟨56697517760977334942745053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 604773522783758239389280565 56697517760977334942745053)
              ·
                refine ⟨21261569160366500603529395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56697517760977334942745053 21261569160366500603529395)
                ·
                  refine ⟨31892353740549750905294093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21261569160366500603529395 31892353740549750905294093)
                  ·
                    refine ⟨11959632652706156589485285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31892353740549750905294093 11959632652706156589485285)
                    ·
                      refine ⟨2242431122382404360528491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11959632652706156589485285 2242431122382404360528491)
                      ·
                        rfl

theorem cell23_4367119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_4367119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367119 prefixEnd_4367119 := by exact prefixLift 4367119
  have htrace : WordTrace (prefixWord ++ tailWord_4367119) baseStart_4367119 baseEnd_4367119 := by
    simpa [prefixWord, tailWord_4367119, baseEnd_4367119] using wordTrace_append hprefix tailTrace_4367119
  have hstable : (prefixWord ++ tailWord_4367119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367119).length < 2 ^ (prefixWord ++ tailWord_4367119).sum := by decide
  have hdescent : baseEnd_4367119 < baseStart_4367119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367136 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4367136 : Nat := 118140960795 + 4367136 * 2 ^ 59
def prefixEnd_4367136 : Nat := 4983230072969 + 3 ^ 40 * 4367136 * 2
def baseEnd_4367136 : Nat := 2242439851553530794015913

theorem tailTrace_4367136 : CollatzResearch.WordTrace tailWord_4367136 prefixEnd_4367136 2242439851553530794015913 := by
  unfold tailWord_4367136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79641267753309797146980631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106188357004413062862640841 79641267753309797146980631)
  ·
    refine ⟨119461901629964695720470947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79641267753309797146980631 119461901629964695720470947)
    ·
      refine ⟨179192852444947043580706421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119461901629964695720470947 179192852444947043580706421)
      ·
        refine ⟨16799329916713785335691227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179192852444947043580706421 16799329916713785335691227)
        ·
          refine ⟨25198994875070678003536841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16799329916713785335691227 25198994875070678003536841)
          ·
            refine ⟨18899246156303008502652631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25198994875070678003536841 18899246156303008502652631)
            ·
              refine ⟨28348869234454512753978947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18899246156303008502652631 28348869234454512753978947)
              ·
                refine ⟨42523303851681769130968421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28348869234454512753978947 42523303851681769130968421)
                ·
                  refine ⟨7973119472190331712056579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42523303851681769130968421 7973119472190331712056579)
                  ·
                    refine ⟨11959679208285497568084869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7973119472190331712056579 11959679208285497568084869)
                    ·
                      refine ⟨2242439851553530794015913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11959679208285497568084869 2242439851553530794015913)
                      ·
                        rfl

theorem cell23_4367136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4367136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367136 prefixEnd_4367136 := by exact prefixLift 4367136
  have htrace : WordTrace (prefixWord ++ tailWord_4367136) baseStart_4367136 baseEnd_4367136 := by
    simpa [prefixWord, tailWord_4367136, baseEnd_4367136] using wordTrace_append hprefix tailTrace_4367136
  have hstable : (prefixWord ++ tailWord_4367136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367136).length < 2 ^ (prefixWord ++ tailWord_4367136).sum := by decide
  have hdescent : baseEnd_4367136 < baseStart_4367136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367213 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4367213 : Nat := 118140960795 + 4367213 * 2 ^ 59
def prefixEnd_4367213 : Nat := 4983230072969 + 3 ^ 40 * 4367213 * 2
def baseEnd_4367213 : Nat := 2242479389563926992753059

theorem tailTrace_4367213 : CollatzResearch.WordTrace tailWord_4367213 prefixEnd_4367213 2242479389563926992753059 := by
  unfold tailWord_4367213
  simp only [CollatzResearch.WordTrace]
  refine ⟨159285343927340636444514293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106190229284893757629676195 159285343927340636444514293)
  ·
    refine ⟨14933000993188184666673215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159285343927340636444514293 14933000993188184666673215)
    ·
      refine ⟨22399501489782277000009823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14933000993188184666673215 22399501489782277000009823)
      ·
        refine ⟨33599252234673415500014735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22399501489782277000009823 33599252234673415500014735)
        ·
          refine ⟨50398878352010123250022103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33599252234673415500014735 50398878352010123250022103)
          ·
            refine ⟨75598317528015184875033155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50398878352010123250022103 75598317528015184875033155)
            ·
              refine ⟨113397476292022777312549733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75598317528015184875033155 113397476292022777312549733)
              ·
                refine ⟨21262026804754270746103075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113397476292022777312549733 21262026804754270746103075)
                ·
                  refine ⟨31893040207131406119154613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21262026804754270746103075 31893040207131406119154613)
                  ·
                    refine ⟨2989972519418569323670745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31893040207131406119154613 2989972519418569323670745)
                    ·
                      refine ⟨2242479389563926992753059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2989972519418569323670745 2242479389563926992753059)
                      ·
                        rfl

theorem cell23_4367213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4367213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367213 prefixEnd_4367213 := by exact prefixLift 4367213
  have htrace : WordTrace (prefixWord ++ tailWord_4367213) baseStart_4367213 baseEnd_4367213 := by
    simpa [prefixWord, tailWord_4367213, baseEnd_4367213] using wordTrace_append hprefix tailTrace_4367213
  have hstable : (prefixWord ++ tailWord_4367213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367213).length < 2 ^ (prefixWord ++ tailWord_4367213).sum := by decide
  have hdescent : baseEnd_4367213 < baseStart_4367213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367237 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 1, 1, 3]
def baseStart_4367237 : Nat := 118140960795 + 4367237 * 2 ^ 59
def prefixEnd_4367237 : Nat := 4983230072969 + 3 ^ 40 * 4367237 * 2
def baseEnd_4367237 : Nat := 2242491713099634898852949

theorem tailTrace_4367237 : CollatzResearch.WordTrace tailWord_4367237 prefixEnd_4367237 2242491713099634898852949 := by
  unfold tailWord_4367237
  simp only [CollatzResearch.WordTrace]
  refine ⟨159286219279253688543387965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106190812852835792362258643 159286219279253688543387965)
  ·
    refine ⟨59732332229720133203770487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159286219279253688543387965 59732332229720133203770487)
    ·
      refine ⟨89598498344580199805655731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59732332229720133203770487 89598498344580199805655731)
      ·
        refine ⟨134397747516870299708483597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89598498344580199805655731 134397747516870299708483597)
        ·
          refine ⟨50399155318826362390681349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134397747516870299708483597 50399155318826362390681349)
          ·
            refine ⟨9449841622279942948252753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50399155318826362390681349 9449841622279942948252753)
            ·
              refine ⟨7087381216709957211189565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9449841622279942948252753 7087381216709957211189565)
              ·
                refine ⟨2657767956266233954196087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7087381216709957211189565 2657767956266233954196087)
                ·
                  refine ⟨3986651934399350931294131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657767956266233954196087 3986651934399350931294131)
                  ·
                    refine ⟨5979977901599026396941197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986651934399350931294131 5979977901599026396941197)
                    ·
                      refine ⟨2242491713099634898852949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5979977901599026396941197 2242491713099634898852949)
                      ·
                        rfl

theorem cell23_4367237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_4367237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367237 prefixEnd_4367237 := by exact prefixLift 4367237
  have htrace : WordTrace (prefixWord ++ tailWord_4367237) baseStart_4367237 baseEnd_4367237 := by
    simpa [prefixWord, tailWord_4367237, baseEnd_4367237] using wordTrace_append hprefix tailTrace_4367237
  have hstable : (prefixWord ++ tailWord_4367237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367237).length < 2 ^ (prefixWord ++ tailWord_4367237).sum := by decide
  have hdescent : baseEnd_4367237 < baseStart_4367237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367240 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 1, 5]
def baseStart_4367240 : Nat := 118140960795 + 4367240 * 2 ^ 59
def prefixEnd_4367240 : Nat := 4983230072969 + 3 ^ 40 * 4367240 * 2
def baseEnd_4367240 : Nat := 747497751180532795705145

theorem tailTrace_4367240 : CollatzResearch.WordTrace tailWord_4367240 prefixEnd_4367240 747497751180532795705145 := by
  unfold tailWord_4367240
  simp only [CollatzResearch.WordTrace]
  refine ⟨79643164349121410027873587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106190885798828546703831449 79643164349121410027873587)
  ·
    refine ⟨119464746523682115041810381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79643164349121410027873587 119464746523682115041810381)
    ·
      refine ⟨44799279946380793140678893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119464746523682115041810381 44799279946380793140678893)
      ·
        refine ⟨16799729979892797427754585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44799279946380793140678893 16799729979892797427754585)
        ·
          refine ⟨12599797484919598070815939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16799729979892797427754585 12599797484919598070815939)
          ·
            refine ⟨18899696227379397106223909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12599797484919598070815939 18899696227379397106223909)
            ·
              refine ⟨3543693042633636957416983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18899696227379397106223909 3543693042633636957416983)
              ·
                refine ⟨5315539563950455436125475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543693042633636957416983 5315539563950455436125475)
                ·
                  refine ⟨7973309345925683154188213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5315539563950455436125475 7973309345925683154188213)
                  ·
                    refine ⟨747497751180532795705145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7973309345925683154188213 747497751180532795705145)
                    ·
                      rfl

theorem cell23_4367240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_4367240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367240 prefixEnd_4367240 := by exact prefixLift 4367240
  have htrace : WordTrace (prefixWord ++ tailWord_4367240) baseStart_4367240 baseEnd_4367240 := by
    simpa [prefixWord, tailWord_4367240, baseEnd_4367240] using wordTrace_append hprefix tailTrace_4367240
  have hstable : (prefixWord ++ tailWord_4367240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367240).length < 2 ^ (prefixWord ++ tailWord_4367240).sum := by decide
  have hdescent : baseEnd_4367240 < baseStart_4367240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367253 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_4367253 : Nat := 118140960795 + 4367253 * 2 ^ 59
def prefixEnd_4367253 : Nat := 4983230072969 + 3 ^ 40 * 4367253 * 2
def baseEnd_4367253 : Nat := 747499976263368945417625

theorem tailTrace_4367253 : CollatzResearch.WordTrace tailWord_4367253 prefixEnd_4367253 747499976263368945417625 := by
  unfold tailWord_4367253
  simp only [CollatzResearch.WordTrace]
  refine ⟨159286802847195723275970413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106191201898130482183980275 159286802847195723275970413)
  ·
    refine ⟨59732551067698396228488905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159286802847195723275970413 59732551067698396228488905)
    ·
      refine ⟨44799413300773797171366679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59732551067698396228488905 44799413300773797171366679)
      ·
        refine ⟨67199119951160695757050019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44799413300773797171366679 67199119951160695757050019)
        ·
          refine ⟨100798679926741043635575029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67199119951160695757050019 100798679926741043635575029)
          ·
            refine ⟨9449876243131972840835159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100798679926741043635575029 9449876243131972840835159)
            ·
              refine ⟨14174814364697959261252739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9449876243131972840835159 14174814364697959261252739)
              ·
                refine ⟨21262221547046938891879109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14174814364697959261252739 21262221547046938891879109)
                ·
                  refine ⟨3986666540071301042227333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21262221547046938891879109 3986666540071301042227333)
                  ·
                    refine ⟨747499976263368945417625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986666540071301042227333 747499976263368945417625)
                    ·
                      rfl

theorem cell23_4367253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_4367253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367253 prefixEnd_4367253 := by exact prefixLift 4367253
  have htrace : WordTrace (prefixWord ++ tailWord_4367253) baseStart_4367253 baseEnd_4367253 := by
    simpa [prefixWord, tailWord_4367253, baseEnd_4367253] using wordTrace_append hprefix tailTrace_4367253
  have hstable : (prefixWord ++ tailWord_4367253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367253).length < 2 ^ (prefixWord ++ tailWord_4367253).sum := by decide
  have hdescent : baseEnd_4367253 < baseStart_4367253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367254 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4367254 : Nat := 118140960795 + 4367254 * 2 ^ 59
def prefixEnd_4367254 : Nat := 4983230072969 + 3 ^ 40 * 4367254 * 2
def baseEnd_4367254 : Nat := 2242500442270761332340371

theorem tailTrace_4367254 : CollatzResearch.WordTrace tailWord_4367254 prefixEnd_4367254 2242500442270761332340371 := by
  unfold tailWord_4367254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955427457512006277922301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106191226213461400297837877 9955427457512006277922301)
  ·
    refine ⟨3733285296567002354220863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9955427457512006277922301 3733285296567002354220863)
    ·
      refine ⟨5599927944850503531331295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3733285296567002354220863 5599927944850503531331295)
      ·
        refine ⟨8399891917275755296996943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599927944850503531331295 8399891917275755296996943)
        ·
          refine ⟨12599837875913632945495415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399891917275755296996943 12599837875913632945495415)
          ·
            refine ⟨18899756813870449418243123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12599837875913632945495415 18899756813870449418243123)
            ·
              refine ⟨28349635220805674127364685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18899756813870449418243123 28349635220805674127364685)
              ·
                refine ⟨10631113207802127797761757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28349635220805674127364685 10631113207802127797761757)
                ·
                  refine ⟨3986667452925797924160659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10631113207802127797761757 3986667452925797924160659)
                  ·
                    refine ⟨5980001179388696886240989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986667452925797924160659 5980001179388696886240989)
                    ·
                      refine ⟨2242500442270761332340371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980001179388696886240989 2242500442270761332340371)
                      ·
                        rfl

theorem cell23_4367254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4367254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367254 prefixEnd_4367254 := by exact prefixLift 4367254
  have htrace : WordTrace (prefixWord ++ tailWord_4367254) baseStart_4367254 baseEnd_4367254 := by
    simpa [prefixWord, tailWord_4367254, baseEnd_4367254] using wordTrace_append hprefix tailTrace_4367254
  have hstable : (prefixWord ++ tailWord_4367254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367254).length < 2 ^ (prefixWord ++ tailWord_4367254).sum := by decide
  have hdescent : baseEnd_4367254 < baseStart_4367254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367263 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4367263 : Nat := 118140960795 + 4367263 * 2 ^ 59
def prefixEnd_4367263 : Nat := 4983230072969 + 3 ^ 40 * 4367263 * 2
def baseEnd_4367263 : Nat := 2242505063596651797127829

theorem tailTrace_4367263 : CollatzResearch.WordTrace tailWord_4367263 prefixEnd_4367263 2242505063596651797127829 := by
  unfold tailWord_4367263
  simp only [CollatzResearch.WordTrace]
  refine ⟨159287167577159494983834443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106191445051439663322556295 159287167577159494983834443)
  ·
    refine ⟨238930751365739242475751665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159287167577159494983834443 238930751365739242475751665)
    ·
      refine ⟨179198063524304431856813749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238930751365739242475751665 179198063524304431856813749)
      ·
        refine ⟨16799818455403540486576289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179198063524304431856813749 16799818455403540486576289)
        ·
          refine ⟨12599863841552655364932217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16799818455403540486576289 12599863841552655364932217)
          ·
            refine ⟨9449897881164491523699163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12599863841552655364932217 9449897881164491523699163)
            ·
              refine ⟨14174846821746737285548745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9449897881164491523699163 14174846821746737285548745)
              ·
                refine ⟨10631135116310052964161559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14174846821746737285548745 10631135116310052964161559)
                ·
                  refine ⟨15946702674465079446242339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10631135116310052964161559 15946702674465079446242339)
                  ·
                    refine ⟨23920054011697619169363509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15946702674465079446242339 23920054011697619169363509)
                    ·
                      refine ⟨2242505063596651797127829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23920054011697619169363509 2242505063596651797127829)
                      ·
                        rfl

theorem cell23_4367263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4367263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367263 prefixEnd_4367263 := by exact prefixLift 4367263
  have htrace : WordTrace (prefixWord ++ tailWord_4367263) baseStart_4367263 baseEnd_4367263 := by
    simpa [prefixWord, tailWord_4367263, baseEnd_4367263] using wordTrace_append hprefix tailTrace_4367263
  have hstable : (prefixWord ++ tailWord_4367263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367263).length < 2 ^ (prefixWord ++ tailWord_4367263).sum := by decide
  have hdescent : baseEnd_4367263 < baseStart_4367263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367300 : List Nat := [2, 3, 3, 3, 1, 2, 9]
def baseStart_4367300 : Nat := 118140960795 + 4367300 * 2 ^ 59
def prefixEnd_4367300 : Nat := 4983230072969 + 3 ^ 40 * 4367300 * 2
def baseEnd_4367300 : Nat := 27685482251615656202039

theorem tailTrace_4367300 : CollatzResearch.WordTrace tailWord_4367300 prefixEnd_4367300 27685482251615656202039 := by
  unfold tailWord_4367300
  simp only [CollatzResearch.WordTrace]
  refine ⟨79644258539012725151465677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106192344718683633535287569 79644258539012725151465677)
  ·
    refine ⟨29866596952129771931799629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79644258539012725151465677 29866596952129771931799629)
    ·
      refine ⟨11199973857048664474424861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29866596952129771931799629 11199973857048664474424861)
      ·
        refine ⟨4199990196393249177909323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11199973857048664474424861 4199990196393249177909323)
        ·
          refine ⟨6299985294589873766863985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4199990196393249177909323 6299985294589873766863985)
          ·
            refine ⟨4724988970942405325147989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6299985294589873766863985 4724988970942405325147989)
            ·
              refine ⟨27685482251615656202039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4724988970942405325147989 27685482251615656202039)
              ·
                rfl

theorem cell23_4367300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 9].length) (baseStart_4367300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367300 prefixEnd_4367300 := by exact prefixLift 4367300
  have htrace : WordTrace (prefixWord ++ tailWord_4367300) baseStart_4367300 baseEnd_4367300 := by
    simpa [prefixWord, tailWord_4367300, baseEnd_4367300] using wordTrace_append hprefix tailTrace_4367300
  have hstable : (prefixWord ++ tailWord_4367300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367300).length < 2 ^ (prefixWord ++ tailWord_4367300).sum := by decide
  have hdescent : baseEnd_4367300 < baseStart_4367300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367306 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_4367306 : Nat := 118140960795 + 4367306 * 2 ^ 59
def prefixEnd_4367306 : Nat := 4983230072969 + 3 ^ 40 * 4367306 * 2
def baseEnd_4367306 : Nat := 2242527143264795128890131

theorem tailTrace_4367306 : CollatzResearch.WordTrace tailWord_4367306 prefixEnd_4367306 2242527143264795128890131 := by
  unfold tailWord_4367306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39822183979000928331912443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106192490610669142218433181 39822183979000928331912443)
  ·
    refine ⟨59733275968501392497868665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39822183979000928331912443 59733275968501392497868665)
    ·
      refine ⟨44799956976376044373401499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59733275968501392497868665 44799956976376044373401499)
      ·
        refine ⟨67199935464564066560102249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44799956976376044373401499 67199935464564066560102249)
        ·
          refine ⟨50399951598423049920076687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67199935464564066560102249 50399951598423049920076687)
          ·
            refine ⟨75599927397634574880115031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50399951598423049920076687 75599927397634574880115031)
            ·
              refine ⟨113399891096451862320172547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75599927397634574880115031 113399891096451862320172547)
              ·
                refine ⟨170099836644677793480258821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113399891096451862320172547 170099836644677793480258821)
                ·
                  refine ⟨31893719370877086277548529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170099836644677793480258821 31893719370877086277548529)
                  ·
                    refine ⟨23920289528157814708161397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31893719370877086277548529 23920289528157814708161397)
                    ·
                      refine ⟨2242527143264795128890131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23920289528157814708161397 2242527143264795128890131)
                      ·
                        rfl

theorem cell23_4367306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_4367306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367306 prefixEnd_4367306 := by exact prefixLift 4367306
  have htrace : WordTrace (prefixWord ++ tailWord_4367306) baseStart_4367306 baseEnd_4367306 := by
    simpa [prefixWord, tailWord_4367306, baseEnd_4367306] using wordTrace_append hprefix tailTrace_4367306
  have hstable : (prefixWord ++ tailWord_4367306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367306).length < 2 ^ (prefixWord ++ tailWord_4367306).sum := by decide
  have hdescent : baseEnd_4367306 < baseStart_4367306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367310 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_4367310 : Nat := 118140960795 + 4367310 * 2 ^ 59
def prefixEnd_4367310 : Nat := 4983230072969 + 3 ^ 40 * 4367310 * 2
def baseEnd_4367310 : Nat := 2242529197187413113240113

theorem tailTrace_4367310 : CollatzResearch.WordTrace tailWord_4367310 prefixEnd_4367310 2242529197187413113240113 := by
  unfold tailWord_4367310
  simp only [CollatzResearch.WordTrace]
  refine ⟨19911110225998652751349423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106192587871992814673863589 19911110225998652751349423)
  ·
    refine ⟨29866665338997979127024135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19911110225998652751349423 29866665338997979127024135)
    ·
      refine ⟨44799998008496968690536203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29866665338997979127024135 44799998008496968690536203)
      ·
        refine ⟨67199997012745453035804305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44799998008496968690536203 67199997012745453035804305)
        ·
          refine ⟨50399997759559089776853229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67199997012745453035804305 50399997759559089776853229)
          ·
            refine ⟨18899999159834658666319961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50399997759559089776853229 18899999159834658666319961)
            ·
              refine ⟨14174999369875993999739971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18899999159834658666319961 14174999369875993999739971)
              ·
                refine ⟨21262499054813990999609957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14174999369875993999739971 21262499054813990999609957)
                ·
                  refine ⟨3986718572777623312426867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21262499054813990999609957 3986718572777623312426867)
                  ·
                    refine ⟨5980077859166434968640301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986718572777623312426867 5980077859166434968640301)
                    ·
                      refine ⟨2242529197187413113240113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980077859166434968640301 2242529197187413113240113)
                      ·
                        rfl

theorem cell23_4367310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_4367310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367310 prefixEnd_4367310 := by exact prefixLift 4367310
  have htrace : WordTrace (prefixWord ++ tailWord_4367310) baseStart_4367310 baseEnd_4367310 := by
    simpa [prefixWord, tailWord_4367310, baseEnd_4367310] using wordTrace_append hprefix tailTrace_4367310
  have hstable : (prefixWord ++ tailWord_4367310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367310).length < 2 ^ (prefixWord ++ tailWord_4367310).sum := by decide
  have hdescent : baseEnd_4367310 < baseStart_4367310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367327 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 3]
def baseStart_4367327 : Nat := 118140960795 + 4367327 * 2 ^ 59
def prefixEnd_4367327 : Nat := 4983230072969 + 3 ^ 40 * 4367327 * 2
def baseEnd_4367327 : Nat := 2242537926358539546727535

theorem tailTrace_4367327 : CollatzResearch.WordTrace tailWord_4367327 prefixEnd_4367327 2242537926358539546727535 := by
  unfold tailWord_4367327
  simp only [CollatzResearch.WordTrace]
  refine ⟨159289501848927633914164235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106193001232618422609442823 159289501848927633914164235)
  ·
    refine ⟨238934252773391450871246353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159289501848927633914164235 238934252773391450871246353)
    ·
      refine ⟨179200689580043588153434765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238934252773391450871246353 179200689580043588153434765)
      ·
        refine ⟨67200258592516345557538037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179200689580043588153434765 67200258592516345557538037)
        ·
          refine ⟨6300024243048407396019191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67200258592516345557538037 6300024243048407396019191)
          ·
            refine ⟨9450036364572611094028787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6300024243048407396019191 9450036364572611094028787)
            ·
              refine ⟨14175054546858916641043181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9450036364572611094028787 14175054546858916641043181)
              ·
                refine ⟨5315645455072093740391193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14175054546858916641043181 5315645455072093740391193)
                ·
                  refine ⟨3986734091304070305293395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5315645455072093740391193 3986734091304070305293395)
                  ·
                    refine ⟨5980101136956105457940093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986734091304070305293395 5980101136956105457940093)
                    ·
                      refine ⟨2242537926358539546727535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980101136956105457940093 2242537926358539546727535)
                      ·
                        rfl

theorem cell23_4367327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_4367327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367327 prefixEnd_4367327 := by exact prefixLift 4367327
  have htrace : WordTrace (prefixWord ++ tailWord_4367327) baseStart_4367327 baseEnd_4367327 := by
    simpa [prefixWord, tailWord_4367327, baseEnd_4367327] using wordTrace_append hprefix tailTrace_4367327
  have hstable : (prefixWord ++ tailWord_4367327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367327).length < 2 ^ (prefixWord ++ tailWord_4367327).sum := by decide
  have hdescent : baseEnd_4367327 < baseStart_4367327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367348 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4367348 : Nat := 118140960795 + 4367348 * 2 ^ 59
def prefixEnd_4367348 : Nat := 4983230072969 + 3 ^ 40 * 4367348 * 2
def baseEnd_4367348 : Nat := 2242548709452283964564939

theorem tailTrace_4367348 : CollatzResearch.WordTrace tailWord_4367348 prefixEnd_4367348 2242548709452283964564939 := by
  unfold tailWord_4367348
  simp only [CollatzResearch.WordTrace]
  refine ⟨79645133890925777250339349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106193511854567703000452465 79645133890925777250339349)
  ·
    refine ⟨3733365651137145808609657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79645133890925777250339349 3733365651137145808609657)
    ·
      refine ⟨2800024238352859356457243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3733365651137145808609657 2800024238352859356457243)
      ·
        refine ⟨4200036357529289034685865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800024238352859356457243 4200036357529289034685865)
        ·
          refine ⟨3150027268146966776014399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4200036357529289034685865 3150027268146966776014399)
          ·
            refine ⟨4725040902220450164021599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150027268146966776014399 4725040902220450164021599)
            ·
              refine ⟨7087561353330675246032399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725040902220450164021599 7087561353330675246032399)
              ·
                refine ⟨10631342029996012869048599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7087561353330675246032399 10631342029996012869048599)
                ·
                  refine ⟨15947013044994019303572899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10631342029996012869048599 15947013044994019303572899)
                  ·
                    refine ⟨23920519567491028955359349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15947013044994019303572899 23920519567491028955359349)
                    ·
                      refine ⟨2242548709452283964564939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23920519567491028955359349 2242548709452283964564939)
                      ·
                        rfl

theorem cell23_4367348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4367348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367348 prefixEnd_4367348 := by exact prefixLift 4367348
  have htrace : WordTrace (prefixWord ++ tailWord_4367348) baseStart_4367348 baseEnd_4367348 := by
    simpa [prefixWord, tailWord_4367348, baseEnd_4367348] using wordTrace_append hprefix tailTrace_4367348
  have hstable : (prefixWord ++ tailWord_4367348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367348).length < 2 ^ (prefixWord ++ tailWord_4367348).sum := by decide
  have hdescent : baseEnd_4367348 < baseStart_4367348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367362 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4367362 : Nat := 118140960795 + 4367362 * 2 ^ 59
def prefixEnd_4367362 : Nat := 4983230072969 + 3 ^ 40 * 4367362 * 2
def baseEnd_4367362 : Nat := 2242555898181446909789875

theorem tailTrace_4367362 : CollatzResearch.WordTrace tailWord_4367362 prefixEnd_4367362 2242555898181446909789875 := by
  unfold tailWord_4367362
  simp only [CollatzResearch.WordTrace]
  refine ⟨39822694600950208722922085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106193852269200556594458893 39822694600950208722922085)
  ·
    refine ⟨7466755237678164135547891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39822694600950208722922085 7466755237678164135547891)
    ·
      refine ⟨11200132856517246203321837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7466755237678164135547891 11200132856517246203321837)
      ·
        refine ⟨4200049821193967326245689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11200132856517246203321837 4200049821193967326245689)
        ·
          refine ⟨3150037365895475494684267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4200049821193967326245689 3150037365895475494684267)
          ·
            refine ⟨4725056048843213242026401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150037365895475494684267 4725056048843213242026401)
            ·
              refine ⟨3543792036632409931519801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4725056048843213242026401 3543792036632409931519801)
              ·
                refine ⟨2657844027474307448639851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3543792036632409931519801 2657844027474307448639851)
                ·
                  refine ⟨3986766041211461172959777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657844027474307448639851 3986766041211461172959777)
                  ·
                    refine ⟨2990074530908595879719833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3986766041211461172959777 2990074530908595879719833)
                    ·
                      refine ⟨2242555898181446909789875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990074530908595879719833 2242555898181446909789875)
                      ·
                        rfl

theorem cell23_4367362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4367362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367362 prefixEnd_4367362 := by exact prefixLift 4367362
  have htrace : WordTrace (prefixWord ++ tailWord_4367362) baseStart_4367362 baseEnd_4367362 := by
    simpa [prefixWord, tailWord_4367362, baseEnd_4367362] using wordTrace_append hprefix tailTrace_4367362
  have hstable : (prefixWord ++ tailWord_4367362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367362).length < 2 ^ (prefixWord ++ tailWord_4367362).sum := by decide
  have hdescent : baseEnd_4367362 < baseStart_4367362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367423 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_4367423 : Nat := 118140960795 + 4367423 * 2 ^ 59
def prefixEnd_4367423 : Nat := 4983230072969 + 3 ^ 40 * 4367423 * 2
def baseEnd_4367423 : Nat := 2242587220501371171127093

theorem tailTrace_4367423 : CollatzResearch.WordTrace tailWord_4367423 prefixEnd_4367423 2242587220501371171127093 := by
  unfold tailWord_4367423
  simp only [CollatzResearch.WordTrace]
  refine ⟨159293003256579842309658923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106195335504386561539772615 159293003256579842309658923)
  ·
    refine ⟨238939504884869763464488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159293003256579842309658923 238939504884869763464488385)
    ·
      refine ⟨179204628663652322598366289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238939504884869763464488385 179204628663652322598366289)
      ·
        refine ⟨134403471497739241948774717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179204628663652322598366289 134403471497739241948774717)
        ·
          refine ⟨50401301811652215730790519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134403471497739241948774717 50401301811652215730790519)
          ·
            refine ⟨75601952717478323596185779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50401301811652215730790519 75601952717478323596185779)
            ·
              refine ⟨113402929076217485394278669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75601952717478323596185779 113402929076217485394278669)
              ·
                refine ⟨42526098403581557022854501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113402929076217485394278669 42526098403581557022854501)
                ·
                  refine ⟨7973643450671541941785219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42526098403581557022854501 7973643450671541941785219)
                  ·
                    refine ⟨11960465176007312912677829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7973643450671541941785219 11960465176007312912677829)
                    ·
                      refine ⟨2242587220501371171127093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11960465176007312912677829 2242587220501371171127093)
                      ·
                        rfl

theorem cell23_4367423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_4367423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367423 prefixEnd_4367423 := by exact prefixLift 4367423
  have htrace : WordTrace (prefixWord ++ tailWord_4367423) baseStart_4367423 baseEnd_4367423 := by
    simpa [prefixWord, tailWord_4367423, baseEnd_4367423] using wordTrace_append hprefix tailTrace_4367423
  have hstable : (prefixWord ++ tailWord_4367423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367423).length < 2 ^ (prefixWord ++ tailWord_4367423).sum := by decide
  have hdescent : baseEnd_4367423 < baseStart_4367423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367443 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3]
def baseStart_4367443 : Nat := 118140960795 + 4367443 * 2 ^ 59
def prefixEnd_4367443 : Nat := 4983230072969 + 3 ^ 40 * 4367443 * 2
def baseEnd_4367443 : Nat := 2242597490114461092877001

theorem tailTrace_4367443 : CollatzResearch.WordTrace tailWord_4367443 prefixEnd_4367443 2242597490114461092877001 := by
  unfold tailWord_4367443
  simp only [CollatzResearch.WordTrace]
  refine ⟨159293732716507385725386983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106195821811004923816924655 159293732716507385725386983)
  ·
    refine ⟨238940599074761078588080475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159293732716507385725386983 238940599074761078588080475)
    ·
      refine ⟨358410898612141617882120713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238940599074761078588080475 358410898612141617882120713)
      ·
        refine ⟨268808173959106213411590535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358410898612141617882120713 268808173959106213411590535)
        ·
          refine ⟨403212260938659320117385803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268808173959106213411590535 403212260938659320117385803)
          ·
            refine ⟨604818391407988980176078705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403212260938659320117385803 604818391407988980176078705)
            ·
              refine ⟨453613793555991735132059029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604818391407988980176078705 453613793555991735132059029)
              ·
                refine ⟨21263146572937112584315267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 453613793555991735132059029 21263146572937112584315267)
                ·
                  refine ⟨31894719859405668876472901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21263146572937112584315267 31894719859405668876472901)
                  ·
                    refine ⟨5980259973638562914338669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31894719859405668876472901 5980259973638562914338669)
                    ·
                      refine ⟨2242597490114461092877001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980259973638562914338669 2242597490114461092877001)
                      ·
                        rfl

theorem cell23_4367443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_4367443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367443 prefixEnd_4367443 := by exact prefixLift 4367443
  have htrace : WordTrace (prefixWord ++ tailWord_4367443) baseStart_4367443 baseEnd_4367443 := by
    simpa [prefixWord, tailWord_4367443, baseEnd_4367443] using wordTrace_append hprefix tailTrace_4367443
  have hstable : (prefixWord ++ tailWord_4367443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367443).length < 2 ^ (prefixWord ++ tailWord_4367443).sum := by decide
  have hdescent : baseEnd_4367443 < baseStart_4367443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367460 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_4367460 : Nat := 118140960795 + 4367460 * 2 ^ 59
def prefixEnd_4367460 : Nat := 4983230072969 + 3 ^ 40 * 4367460 * 2
def baseEnd_4367460 : Nat := 2242606219285587526364423

theorem tailTrace_4367460 : CollatzResearch.WordTrace tailWord_4367460 prefixEnd_4367460 2242606219285587526364423 := by
  unfold tailWord_4367460
  simp only [CollatzResearch.WordTrace]
  refine ⟨79647176378722898814377917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106196235171630531752503889 79647176378722898814377917)
  ·
    refine ⟨29867691142021087055391719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79647176378722898814377917 29867691142021087055391719)
    ·
      refine ⟨44801536713031630583087579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29867691142021087055391719 44801536713031630583087579)
      ·
        refine ⟨67202305069547445874631369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44801536713031630583087579 67202305069547445874631369)
        ·
          refine ⟨50401728802160584405973527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67202305069547445874631369 50401728802160584405973527)
          ·
            refine ⟨75602593203240876608960291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50401728802160584405973527 75602593203240876608960291)
            ·
              refine ⟨113403889804861314913440437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75602593203240876608960291 113403889804861314913440437)
              ·
                refine ⟨10631614669205748273135041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113403889804861314913440437 10631614669205748273135041)
                ·
                  refine ⟨7973711001904311204851281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10631614669205748273135041 7973711001904311204851281)
                  ·
                    refine ⟨5980283251428233403638461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7973711001904311204851281 5980283251428233403638461)
                    ·
                      refine ⟨2242606219285587526364423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980283251428233403638461 2242606219285587526364423)
                      ·
                        rfl

theorem cell23_4367460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_4367460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367460 prefixEnd_4367460 := by exact prefixLift 4367460
  have htrace : WordTrace (prefixWord ++ tailWord_4367460) baseStart_4367460 baseEnd_4367460 := by
    simpa [prefixWord, tailWord_4367460, baseEnd_4367460] using wordTrace_append hprefix tailTrace_4367460
  have hstable : (prefixWord ++ tailWord_4367460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367460).length < 2 ^ (prefixWord ++ tailWord_4367460).sum := by decide
  have hdescent : baseEnd_4367460 < baseStart_4367460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367463 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 8]
def baseStart_4367463 : Nat := 118140960795 + 4367463 * 2 ^ 59
def prefixEnd_4367463 : Nat := 4983230072969 + 3 ^ 40 * 4367463 * 2
def baseEnd_4367463 : Nat := 249178639969727890514101

theorem tailTrace_4367463 : CollatzResearch.WordTrace tailWord_4367463 prefixEnd_4367463 249178639969727890514101 := by
  unfold tailWord_4367463
  simp only [CollatzResearch.WordTrace]
  refine ⟨159294462176434929141115043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106196308117623286094076695 159294462176434929141115043)
  ·
    refine ⟨238941693264652393711672565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159294462176434929141115043 238941693264652393711672565)
    ·
      refine ⟨22400783743561161910469303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238941693264652393711672565 22400783743561161910469303)
      ·
        refine ⟨33601175615341742865703955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22400783743561161910469303 33601175615341742865703955)
        ·
          refine ⟨50401763423012614298555933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33601175615341742865703955 50401763423012614298555933)
          ·
            refine ⟨18900661283629730361958475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50401763423012614298555933 18900661283629730361958475)
            ·
              refine ⟨28350991925444595542937713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18900661283629730361958475 28350991925444595542937713)
              ·
                refine ⟨21263243944083446657203285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28350991925444595542937713 21263243944083446657203285)
                ·
                  refine ⟨249178639969727890514101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21263243944083446657203285 249178639969727890514101)
                  ·
                    rfl

theorem cell23_4367463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 8].length) (baseStart_4367463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367463 prefixEnd_4367463 := by exact prefixLift 4367463
  have htrace : WordTrace (prefixWord ++ tailWord_4367463) baseStart_4367463 baseEnd_4367463 := by
    simpa [prefixWord, tailWord_4367463, baseEnd_4367463] using wordTrace_append hprefix tailTrace_4367463
  have hstable : (prefixWord ++ tailWord_4367463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367463).length < 2 ^ (prefixWord ++ tailWord_4367463).sum := by decide
  have hdescent : baseEnd_4367463 < baseStart_4367463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367484 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_4367484 : Nat := 118140960795 + 4367484 * 2 ^ 59
def prefixEnd_4367484 : Nat := 4983230072969 + 3 ^ 40 * 4367484 * 2
def baseEnd_4367484 : Nat := 747539514273765144154771

theorem tailTrace_4367484 : CollatzResearch.WordTrace tailWord_4367484 prefixEnd_4367484 747539514273765144154771 := by
  unfold tailWord_4367484
  simp only [CollatzResearch.WordTrace]
  refine ⟨79647614054679424863814753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106196818739572566485086337 79647614054679424863814753)
  ·
    refine ⟨59735710541009568647861065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79647614054679424863814753 59735710541009568647861065)
    ·
      refine ⟨44801782905757176485895799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59735710541009568647861065 44801782905757176485895799)
      ·
        refine ⟨67202674358635764728843699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44801782905757176485895799 67202674358635764728843699)
        ·
          refine ⟨100804011537953647093265549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67202674358635764728843699 100804011537953647093265549)
          ·
            refine ⟨37801504326732617659974581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100804011537953647093265549 37801504326732617659974581)
            ·
              refine ⟨3543891030631182905622617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37801504326732617659974581 3543891030631182905622617)
              ·
                refine ⟨2657918272973387179216963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3543891030631182905622617 2657918272973387179216963)
                ·
                  refine ⟨3986877409460080768825445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657918272973387179216963 3986877409460080768825445)
                  ·
                    refine ⟨747539514273765144154771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986877409460080768825445 747539514273765144154771)
                    ·
                      rfl

theorem cell23_4367484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_4367484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367484 prefixEnd_4367484 := by exact prefixLift 4367484
  have htrace : WordTrace (prefixWord ++ tailWord_4367484) baseStart_4367484 baseEnd_4367484 := by
    simpa [prefixWord, tailWord_4367484, baseEnd_4367484] using wordTrace_append hprefix tailTrace_4367484
  have hstable : (prefixWord ++ tailWord_4367484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367484).length < 2 ^ (prefixWord ++ tailWord_4367484).sum := by decide
  have hdescent : baseEnd_4367484 < baseStart_4367484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367497 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 6]
def baseStart_4367497 : Nat := 118140960795 + 4367497 * 2 ^ 59
def prefixEnd_4367497 : Nat := 4983230072969 + 3 ^ 40 * 4367497 * 2
def baseEnd_4367497 : Nat := 249180579785533764622417

theorem tailTrace_4367497 : CollatzResearch.WordTrace tailWord_4367497 prefixEnd_4367497 249180579785533764622417 := by
  unfold tailWord_4367497
  simp only [CollatzResearch.WordTrace]
  refine ⟨159295702258311752947852745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106197134838874501965235163 159295702258311752947852745)
  ·
    refine ⟨119471776693733814710889559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159295702258311752947852745 119471776693733814710889559)
    ·
      refine ⟨179207665040600722066334339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119471776693733814710889559 179207665040600722066334339)
      ·
        refine ⟨268811497560901083099501509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179207665040600722066334339 268811497560901083099501509)
        ·
          refine ⟨50402155792668953081156533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268811497560901083099501509 50402155792668953081156533)
          ·
            refine ⟨4725202105562714351358425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50402155792668953081156533 4725202105562714351358425)
            ·
              refine ⟨3543901579172035763518819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4725202105562714351358425 3543901579172035763518819)
              ·
                refine ⟨5315852368758053645278229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543901579172035763518819 5315852368758053645278229)
                ·
                  refine ⟨249180579785533764622417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5315852368758053645278229 249180579785533764622417)
                  ·
                    rfl

theorem cell23_4367497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 6].length) (baseStart_4367497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367497 prefixEnd_4367497 := by exact prefixLift 4367497
  have htrace : WordTrace (prefixWord ++ tailWord_4367497) baseStart_4367497 baseEnd_4367497 := by
    simpa [prefixWord, tailWord_4367497, baseEnd_4367497] using wordTrace_append hprefix tailTrace_4367497
  have hstable : (prefixWord ++ tailWord_4367497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367497).length < 2 ^ (prefixWord ++ tailWord_4367497).sum := by decide
  have hdescent : baseEnd_4367497 < baseStart_4367497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367500 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_4367500 : Nat := 118140960795 + 4367500 * 2 ^ 59
def prefixEnd_4367500 : Nat := 4983230072969 + 3 ^ 40 * 4367500 * 2
def baseEnd_4367500 : Nat := 2242626758511767369864239

theorem tailTrace_4367500 : CollatzResearch.WordTrace tailWord_4367500 prefixEnd_4367500 2242626758511767369864239 := by
  unfold tailWord_4367500
  simp only [CollatzResearch.WordTrace]
  refine ⟨79647905838650442230105977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106197207784867256306807969 79647905838650442230105977)
  ·
    refine ⟨59735929378987831672579483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79647905838650442230105977 59735929378987831672579483)
    ·
      refine ⟨89603894068481747508869225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59735929378987831672579483 89603894068481747508869225)
      ·
        refine ⟨67202920551361310631651919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89603894068481747508869225 67202920551361310631651919)
        ·
          refine ⟨100804380827041965947477879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67202920551361310631651919 100804380827041965947477879)
          ·
            refine ⟨151206571240562948921216819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100804380827041965947477879 151206571240562948921216819)
            ·
              refine ⟨226809856860844423381825229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151206571240562948921216819 226809856860844423381825229)
              ·
                refine ⟨85053696322816658768184461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226809856860844423381825229 85053696322816658768184461)
                ·
                  refine ⟨31895136121056247038069173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85053696322816658768184461 31895136121056247038069173)
                  ·
                    refine ⟨2990169011349023159818985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31895136121056247038069173 2990169011349023159818985)
                    ·
                      refine ⟨2242626758511767369864239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990169011349023159818985 2242626758511767369864239)
                      ·
                        rfl

theorem cell23_4367500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_4367500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367500 prefixEnd_4367500 := by exact prefixLift 4367500
  have htrace : WordTrace (prefixWord ++ tailWord_4367500) baseStart_4367500 baseEnd_4367500 := by
    simpa [prefixWord, tailWord_4367500, baseEnd_4367500] using wordTrace_append hprefix tailTrace_4367500
  have hstable : (prefixWord ++ tailWord_4367500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367500).length < 2 ^ (prefixWord ++ tailWord_4367500).sum := by decide
  have hdescent : baseEnd_4367500 < baseStart_4367500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367560 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_4367560 : Nat := 118140960795 + 4367560 * 2 ^ 59
def prefixEnd_4367560 : Nat := 4983230072969 + 3 ^ 40 * 4367560 * 2
def baseEnd_4367560 : Nat := 2242657567351037135113963

theorem tailTrace_4367560 : CollatzResearch.WordTrace tailWord_4367560 prefixEnd_4367560 2242657567351037135113963 := by
  unfold tailWord_4367560
  simp only [CollatzResearch.WordTrace]
  refine ⟨79649000028541757353698067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106198666704722343138264089 79649000028541757353698067)
  ·
    refine ⟨119473500042812636030547101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79649000028541757353698067 119473500042812636030547101)
    ·
      refine ⟨44802562516054738511455163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119473500042812636030547101 44802562516054738511455163)
      ·
        refine ⟨67203843774082107767182745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44802562516054738511455163 67203843774082107767182745)
        ·
          refine ⟨50402882830561580825387059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67203843774082107767182745 50402882830561580825387059)
          ·
            refine ⟨75604324245842371238080589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50402882830561580825387059 75604324245842371238080589)
            ·
              refine ⟨28351621592190889214280221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75604324245842371238080589 28351621592190889214280221)
              ·
                refine ⟨10631858097071583455355083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28351621592190889214280221 10631858097071583455355083)
                ·
                  refine ⟨15947787145607375183032625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10631858097071583455355083 15947787145607375183032625)
                  ·
                    refine ⟨11960840359205531387274469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15947787145607375183032625 11960840359205531387274469)
                    ·
                      refine ⟨2242657567351037135113963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11960840359205531387274469 2242657567351037135113963)
                      ·
                        rfl

theorem cell23_4367560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_4367560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367560 prefixEnd_4367560 := by exact prefixLift 4367560
  have htrace : WordTrace (prefixWord ++ tailWord_4367560) baseStart_4367560 baseEnd_4367560 := by
    simpa [prefixWord, tailWord_4367560, baseEnd_4367560] using wordTrace_append hprefix tailTrace_4367560
  have hstable : (prefixWord ++ tailWord_4367560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367560).length < 2 ^ (prefixWord ++ tailWord_4367560).sum := by decide
  have hdescent : baseEnd_4367560 < baseStart_4367560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367584 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3]
def baseStart_4367584 : Nat := 118140960795 + 4367584 * 2 ^ 59
def prefixEnd_4367584 : Nat := 4983230072969 + 3 ^ 40 * 4367584 * 2
def baseEnd_4367584 : Nat := 2242669890886745041213853

theorem tailTrace_4367584 : CollatzResearch.WordTrace tailWord_4367584 prefixEnd_4367584 2242669890886745041213853 := by
  unfold tailWord_4367584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79649437704498283403134903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106199250272664377870846537 79649437704498283403134903)
  ·
    refine ⟨119474156556747425104702355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79649437704498283403134903 119474156556747425104702355)
    ·
      refine ⟨179211234835121137657053533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119474156556747425104702355 179211234835121137657053533)
      ·
        refine ⟨67204213063170426621395075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179211234835121137657053533 67204213063170426621395075)
        ·
          refine ⟨100806319594755639932092613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67204213063170426621395075 100806319594755639932092613)
          ·
            refine ⟨18901184924016682487267365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100806319594755639932092613 18901184924016682487267365)
            ·
              refine ⟨3543972173253127966362631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18901184924016682487267365 3543972173253127966362631)
              ·
                refine ⟨5315958259879691949543947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543972173253127966362631 5315958259879691949543947)
                ·
                  refine ⟨7973937389819537924315921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5315958259879691949543947 7973937389819537924315921)
                  ·
                    refine ⟨5980453042364653443236941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7973937389819537924315921 5980453042364653443236941)
                    ·
                      refine ⟨2242669890886745041213853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980453042364653443236941 2242669890886745041213853)
                      ·
                        rfl

theorem cell23_4367584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_4367584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367584 prefixEnd_4367584 := by exact prefixLift 4367584
  have htrace : WordTrace (prefixWord ++ tailWord_4367584) baseStart_4367584 baseEnd_4367584 := by
    simpa [prefixWord, tailWord_4367584, baseEnd_4367584] using wordTrace_append hprefix tailTrace_4367584
  have hstable : (prefixWord ++ tailWord_4367584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367584).length < 2 ^ (prefixWord ++ tailWord_4367584).sum := by decide
  have hdescent : baseEnd_4367584 < baseStart_4367584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367591 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4367591 : Nat := 118140960795 + 4367591 * 2 ^ 59
def prefixEnd_4367591 : Nat := 4983230072969 + 3 ^ 40 * 4367591 * 2
def baseEnd_4367591 : Nat := 747557828417108837942107

theorem tailTrace_4367591 : CollatzResearch.WordTrace tailWord_4367591 prefixEnd_4367591 747557828417108837942107 := by
  unfold tailWord_4367591
  simp only [CollatzResearch.WordTrace]
  refine ⟨159299130719971207001774627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106199420479980804667849751 159299130719971207001774627)
  ·
    refine ⟨238948696079956810502661941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159299130719971207001774627 238948696079956810502661941)
    ·
      refine ⟨22401440257495950984624557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238948696079956810502661941 22401440257495950984624557)
      ·
        refine ⟨8400540096560981619234209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22401440257495950984624557 8400540096560981619234209)
        ·
          refine ⟨6300405072420736214425657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8400540096560981619234209 6300405072420736214425657)
          ·
            refine ⟨4725303804315552160819243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6300405072420736214425657 4725303804315552160819243)
            ·
              refine ⟨7087955706473328241228865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725303804315552160819243 7087955706473328241228865)
              ·
                refine ⟨5315966779854996180921649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7087955706473328241228865 5315966779854996180921649)
                ·
                  refine ⟨3986975084891247135691237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5315966779854996180921649 3986975084891247135691237)
                  ·
                    refine ⟨747557828417108837942107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986975084891247135691237 747557828417108837942107)
                    ·
                      rfl

theorem cell23_4367591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4367591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367591 prefixEnd_4367591 := by exact prefixLift 4367591
  have htrace : WordTrace (prefixWord ++ tailWord_4367591) baseStart_4367591 baseEnd_4367591 := by
    simpa [prefixWord, tailWord_4367591, baseEnd_4367591] using wordTrace_append hprefix tailTrace_4367591
  have hstable : (prefixWord ++ tailWord_4367591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367591).length < 2 ^ (prefixWord ++ tailWord_4367591).sum := by decide
  have hdescent : baseEnd_4367591 < baseStart_4367591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367593 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_4367593 : Nat := 118140960795 + 4367593 * 2 ^ 59
def prefixEnd_4367593 : Nat := 4983230072969 + 3 ^ 40 * 4367593 * 2
def baseEnd_4367593 : Nat := 2242674512212635506001311

theorem tailTrace_4367593 : CollatzResearch.WordTrace tailWord_4367593 prefixEnd_4367593 2242674512212635506001311 := by
  unfold tailWord_4367593
  simp only [CollatzResearch.WordTrace]
  refine ⟨159299203665963961343347433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106199469110642640895564955 159299203665963961343347433)
  ·
    refine ⟨119474402749472971007510575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159299203665963961343347433 119474402749472971007510575)
    ·
      refine ⟨179211604124209456511265863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119474402749472971007510575 179211604124209456511265863)
      ·
        refine ⟨268817406186314184766898795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179211604124209456511265863 268817406186314184766898795)
        ·
          refine ⟨403226109279471277150348193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268817406186314184766898795 403226109279471277150348193)
          ·
            refine ⟨302419581959603457862761145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403226109279471277150348193 302419581959603457862761145)
            ·
              refine ⟨226814686469702593397070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302419581959603457862761145 226814686469702593397070859)
              ·
                refine ⟨340222029704553890095606289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226814686469702593397070859 340222029704553890095606289)
                ·
                  refine ⟨255166522278415417571704717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340222029704553890095606289 255166522278415417571704717)
                  ·
                    refine ⟨95687445854405781589389269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255166522278415417571704717 95687445854405781589389269)
                    ·
                      refine ⟨2242674512212635506001311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95687445854405781589389269 2242674512212635506001311)
                      ·
                        rfl

theorem cell23_4367593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_4367593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367593 prefixEnd_4367593 := by exact prefixLift 4367593
  have htrace : WordTrace (prefixWord ++ tailWord_4367593) baseStart_4367593 baseEnd_4367593 := by
    simpa [prefixWord, tailWord_4367593, baseEnd_4367593] using wordTrace_append hprefix tailTrace_4367593
  have hstable : (prefixWord ++ tailWord_4367593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367593).length < 2 ^ (prefixWord ++ tailWord_4367593).sum := by decide
  have hdescent : baseEnd_4367593 < baseStart_4367593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367614 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4367614 : Nat := 118140960795 + 4367614 * 2 ^ 59
def prefixEnd_4367614 : Nat := 4983230072969 + 3 ^ 40 * 4367614 * 2
def baseEnd_4367614 : Nat := 2242685295306379923838715

theorem tailTrace_4367614 : CollatzResearch.WordTrace tailWord_4367614 prefixEnd_4367614 2242685295306379923838715 := by
  unfold tailWord_4367614
  simp only [CollatzResearch.WordTrace]
  refine ⟨19912496199860985241232737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106199979732591921286574597 19912496199860985241232737)
  ·
    refine ⟨14934372149895738930924553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19912496199860985241232737 14934372149895738930924553)
    ·
      refine ⟨11200779112421804198193415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14934372149895738930924553 11200779112421804198193415)
      ·
        refine ⟨16801168668632706297290123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11200779112421804198193415 16801168668632706297290123)
        ·
          refine ⟨25201753002949059445935185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16801168668632706297290123 25201753002949059445935185)
          ·
            refine ⟨18901314752211794584451389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25201753002949059445935185 18901314752211794584451389)
            ·
              refine ⟨7087993032079422969169271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18901314752211794584451389 7087993032079422969169271)
              ·
                refine ⟨10631989548119134453753907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7087993032079422969169271 10631989548119134453753907)
                ·
                  refine ⟨15947984322178701680630861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10631989548119134453753907 15947984322178701680630861)
                  ·
                    refine ⟨5980494120817013130236573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15947984322178701680630861 5980494120817013130236573)
                    ·
                      refine ⟨2242685295306379923838715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980494120817013130236573 2242685295306379923838715)
                      ·
                        rfl

theorem cell23_4367614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4367614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367614 prefixEnd_4367614 := by exact prefixLift 4367614
  have htrace : WordTrace (prefixWord ++ tailWord_4367614) baseStart_4367614 baseEnd_4367614 := by
    simpa [prefixWord, tailWord_4367614, baseEnd_4367614] using wordTrace_append hprefix tailTrace_4367614
  have hstable : (prefixWord ++ tailWord_4367614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367614).length < 2 ^ (prefixWord ++ tailWord_4367614).sum := by decide
  have hdescent : baseEnd_4367614 < baseStart_4367614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367637 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_4367637 : Nat := 118140960795 + 4367637 * 2 ^ 59
def prefixEnd_4367637 : Nat := 4983230072969 + 3 ^ 40 * 4367637 * 2
def baseEnd_4367637 : Nat := 2242697105361433333851109

theorem tailTrace_4367637 : CollatzResearch.WordTrace tailWord_4367637 prefixEnd_4367637 2242697105361433333851109 := by
  unfold tailWord_4367637
  simp only [CollatzResearch.WordTrace]
  refine ⟨159300808477804556857949165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106200538985203037905299443 159300808477804556857949165)
  ·
    refine ⟨59737803179176708821730937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159300808477804556857949165 59737803179176708821730937)
    ·
      refine ⟨44803352384382531616298203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59737803179176708821730937 44803352384382531616298203)
      ·
        refine ⟨67205028576573797424447305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44803352384382531616298203 67205028576573797424447305)
        ·
          refine ⟨50403771432430348068335479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67205028576573797424447305 50403771432430348068335479)
          ·
            refine ⟨75605657148645522102503219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50403771432430348068335479 75605657148645522102503219)
            ·
              refine ⟨113408485722968283153754829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75605657148645522102503219 113408485722968283153754829)
              ·
                refine ⟨42528182146113106182658061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113408485722968283153754829 42528182146113106182658061)
                ·
                  refine ⟨15948068304792414818496773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42528182146113106182658061 15948068304792414818496773)
                  ·
                    refine ⟨2990262807148577778468145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15948068304792414818496773 2990262807148577778468145)
                    ·
                      refine ⟨2242697105361433333851109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990262807148577778468145 2242697105361433333851109)
                      ·
                        rfl

theorem cell23_4367637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_4367637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367637 prefixEnd_4367637 := by exact prefixLift 4367637
  have htrace : WordTrace (prefixWord ++ tailWord_4367637) baseStart_4367637 baseEnd_4367637 := by
    simpa [prefixWord, tailWord_4367637, baseEnd_4367637] using wordTrace_append hprefix tailTrace_4367637
  have hstable : (prefixWord ++ tailWord_4367637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367637).length < 2 ^ (prefixWord ++ tailWord_4367637).sum := by decide
  have hdescent : baseEnd_4367637 < baseStart_4367637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367640 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4367640 : Nat := 118140960795 + 4367640 * 2 ^ 59
def prefixEnd_4367640 : Nat := 4983230072969 + 3 ^ 40 * 4367640 * 2
def baseEnd_4367640 : Nat := 2242698645803396822113595

theorem tailTrace_4367640 : CollatzResearch.WordTrace tailWord_4367640 prefixEnd_4367640 2242698645803396822113595 := by
  unfold tailWord_4367640
  simp only [CollatzResearch.WordTrace]
  refine ⟨79650458948396844185154187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106200611931195792246872249 79650458948396844185154187)
  ·
    refine ⟨119475688422595266277731281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79650458948396844185154187 119475688422595266277731281)
    ·
      refine ⟨89606766316946449708298461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119475688422595266277731281 89606766316946449708298461)
      ·
        refine ⟨33602537368854918640611923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89606766316946449708298461 33602537368854918640611923)
        ·
          refine ⟨50403806053282377960917885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33602537368854918640611923 50403806053282377960917885)
          ·
            refine ⟨18901427269980891735344207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50403806053282377960917885 18901427269980891735344207)
            ·
              refine ⟨28352140904971337603016311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18901427269980891735344207 28352140904971337603016311)
              ·
                refine ⟨42528211357457006404524467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28352140904971337603016311 42528211357457006404524467)
                ·
                  refine ⟨63792317036185509606786701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42528211357457006404524467 63792317036185509606786701)
                  ·
                    refine ⟨23922118888569566102545013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63792317036185509606786701 23922118888569566102545013)
                    ·
                      refine ⟨2242698645803396822113595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23922118888569566102545013 2242698645803396822113595)
                      ·
                        rfl

theorem cell23_4367640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4367640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367640 prefixEnd_4367640 := by exact prefixLift 4367640
  have htrace : WordTrace (prefixWord ++ tailWord_4367640) baseStart_4367640 baseEnd_4367640 := by
    simpa [prefixWord, tailWord_4367640, baseEnd_4367640] using wordTrace_append hprefix tailTrace_4367640
  have hstable : (prefixWord ++ tailWord_4367640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367640).length < 2 ^ (prefixWord ++ tailWord_4367640).sum := by decide
  have hdescent : baseEnd_4367640 < baseStart_4367640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367690 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_4367690 : Nat := 118140960795 + 4367690 * 2 ^ 59
def prefixEnd_4367690 : Nat := 4983230072969 + 3 ^ 40 * 4367690 * 2
def baseEnd_4367690 : Nat := 747574773278707208829455

theorem tailTrace_4367690 : CollatzResearch.WordTrace tailWord_4367690 prefixEnd_4367690 747574773278707208829455 := by
  unfold tailWord_4367690
  simp only [CollatzResearch.WordTrace]
  refine ⟨39825685386653136727407131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106201827697741697939752349 39825685386653136727407131)
  ·
    refine ⟨59738528079979705091110697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39825685386653136727407131 59738528079979705091110697)
    ·
      refine ⟨44803896059984778818333023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59738528079979705091110697 44803896059984778818333023)
      ·
        refine ⟨67205844089977168227499535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44803896059984778818333023 67205844089977168227499535)
        ·
          refine ⟨100808766134965752341249303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67205844089977168227499535 100808766134965752341249303)
          ·
            refine ⟨151213149202448628511873955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100808766134965752341249303 151213149202448628511873955)
            ·
              refine ⟨226819723803672942767810933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151213149202448628511873955 226819723803672942767810933)
              ·
                refine ⟨21264349106594338384482275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226819723803672942767810933 21264349106594338384482275)
                ·
                  refine ⟨31896523659891507576723413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21264349106594338384482275 31896523659891507576723413)
                  ·
                    refine ⟨747574773278707208829455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31896523659891507576723413 747574773278707208829455)
                    ·
                      rfl

theorem cell23_4367690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_4367690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367690 prefixEnd_4367690 := by exact prefixLift 4367690
  have htrace : WordTrace (prefixWord ++ tailWord_4367690) baseStart_4367690 baseEnd_4367690 := by
    simpa [prefixWord, tailWord_4367690, baseEnd_4367690] using wordTrace_append hprefix tailTrace_4367690
  have hstable : (prefixWord ++ tailWord_4367690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367690).length < 2 ^ (prefixWord ++ tailWord_4367690).sum := by decide
  have hdescent : baseEnd_4367690 < baseStart_4367690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367714 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4367714 : Nat := 118140960795 + 4367714 * 2 ^ 59
def prefixEnd_4367714 : Nat := 4983230072969 + 3 ^ 40 * 4367714 * 2
def baseEnd_4367714 : Nat := 2242736643371829532588255

theorem tailTrace_4367714 : CollatzResearch.WordTrace tailWord_4367714 prefixEnd_4367714 2242736643371829532588255 := by
  unfold tailWord_4367714
  simp only [CollatzResearch.WordTrace]
  refine ⟨39825904224631399752125549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106202411265683732672334797 39825904224631399752125549)
  ·
    refine ⟨14934714084236774907047081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39825904224631399752125549 14934714084236774907047081)
    ·
      refine ⟨11201035563177581180285311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14934714084236774907047081 11201035563177581180285311)
      ·
        refine ⟨16801553344766371770427967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11201035563177581180285311 16801553344766371770427967)
        ·
          refine ⟨25202330017149557655641951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16801553344766371770427967 25202330017149557655641951)
          ·
            refine ⟨37803495025724336483462927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25202330017149557655641951 37803495025724336483462927)
            ·
              refine ⟨56705242538586504725194391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37803495025724336483462927 56705242538586504725194391)
              ·
                refine ⟨85057863807879757087791587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56705242538586504725194391 85057863807879757087791587)
                ·
                  refine ⟨127586795711819635631687381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85057863807879757087791587 127586795711819635631687381)
                  ·
                    refine ⟨2990315524495772710117673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 127586795711819635631687381 2990315524495772710117673)
                    ·
                      refine ⟨2242736643371829532588255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990315524495772710117673 2242736643371829532588255)
                      ·
                        rfl

theorem cell23_4367714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4367714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367714 prefixEnd_4367714 := by exact prefixLift 4367714
  have htrace : WordTrace (prefixWord ++ tailWord_4367714) baseStart_4367714 baseEnd_4367714 := by
    simpa [prefixWord, tailWord_4367714, baseEnd_4367714] using wordTrace_append hprefix tailTrace_4367714
  have hstable : (prefixWord ++ tailWord_4367714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367714).length < 2 ^ (prefixWord ++ tailWord_4367714).sum := by decide
  have hdescent : baseEnd_4367714 < baseStart_4367714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367737 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_4367737 : Nat := 118140960795 + 4367737 * 2 ^ 59
def prefixEnd_4367737 : Nat := 4983230072969 + 3 ^ 40 * 4367737 * 2
def baseEnd_4367737 : Nat := 747582817808960980866883

theorem tailTrace_4367737 : CollatzResearch.WordTrace tailWord_4367737 prefixEnd_4367737 747582817808960980866883 := by
  unfold tailWord_4367737
  simp only [CollatzResearch.WordTrace]
  refine ⟨159304455777442273936589465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106202970518294849291059643 159304455777442273936589465)
  ·
    refine ⟨119478341833081705452442099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159304455777442273936589465 119478341833081705452442099)
    ·
      refine ⟨179217512749622558178663149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119478341833081705452442099 179217512749622558178663149)
      ·
        refine ⟨67206567281108459316998681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179217512749622558178663149 67206567281108459316998681)
        ·
          refine ⟨50404925460831344487749011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67206567281108459316998681 50404925460831344487749011)
          ·
            refine ⟨75607388191247016731623517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50404925460831344487749011 75607388191247016731623517)
            ·
              refine ⟨28352770571717631274358819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75607388191247016731623517 28352770571717631274358819)
              ·
                refine ⟨42529155857576446911538229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28352770571717631274358819 42529155857576446911538229)
                ·
                  refine ⟨3987108361647791897956709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42529155857576446911538229 3987108361647791897956709)
                  ·
                    refine ⟨747582817808960980866883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3987108361647791897956709 747582817808960980866883)
                    ·
                      rfl

theorem cell23_4367737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_4367737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367737 prefixEnd_4367737 := by exact prefixLift 4367737
  have htrace : WordTrace (prefixWord ++ tailWord_4367737) baseStart_4367737 baseEnd_4367737 := by
    simpa [prefixWord, tailWord_4367737, baseEnd_4367737] using wordTrace_append hprefix tailTrace_4367737
  have hstable : (prefixWord ++ tailWord_4367737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367737).length < 2 ^ (prefixWord ++ tailWord_4367737).sum := by decide
  have hdescent : baseEnd_4367737 < baseStart_4367737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367794 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_4367794 : Nat := 118140960795 + 4367794 * 2 ^ 59
def prefixEnd_4367794 : Nat := 4983230072969 + 3 ^ 40 * 4367794 * 2
def baseEnd_4367794 : Nat := 2242777721824189219587887

theorem tailTrace_4367794 : CollatzResearch.WordTrace tailWord_4367794 prefixEnd_4367794 2242777721824189219587887 := by
  unfold tailWord_4367794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39826633684558943167853609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106204356492157181780942957 39826633684558943167853609)
  ·
    refine ⟨29869975263419207375890207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39826633684558943167853609 29869975263419207375890207)
    ·
      refine ⟨44804962895128811063835311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29869975263419207375890207 44804962895128811063835311)
      ·
        refine ⟨67207444342693216595752967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44804962895128811063835311 67207444342693216595752967)
        ·
          refine ⟨100811166514039824893629451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67207444342693216595752967 100811166514039824893629451)
          ·
            refine ⟨151216749771059737340444177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100811166514039824893629451 151216749771059737340444177)
            ·
              refine ⟨113412562328294803005333133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151216749771059737340444177 113412562328294803005333133)
              ·
                refine ⟨42529710873110551126999925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113412562328294803005333133 42529710873110551126999925)
                ·
                  refine ⟨3987160394354114168156243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42529710873110551126999925 3987160394354114168156243)
                  ·
                    refine ⟨5980740591531171252234365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3987160394354114168156243 5980740591531171252234365)
                    ·
                      refine ⟨2242777721824189219587887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980740591531171252234365 2242777721824189219587887)
                      ·
                        rfl

theorem cell23_4367794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_4367794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367794 prefixEnd_4367794 := by exact prefixLift 4367794
  have htrace : WordTrace (prefixWord ++ tailWord_4367794) baseStart_4367794 baseEnd_4367794 := by
    simpa [prefixWord, tailWord_4367794, baseEnd_4367794] using wordTrace_append hprefix tailTrace_4367794
  have hstable : (prefixWord ++ tailWord_4367794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367794).length < 2 ^ (prefixWord ++ tailWord_4367794).sum := by decide
  have hdescent : baseEnd_4367794 < baseStart_4367794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367817 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_4367817 : Nat := 118140960795 + 4367817 * 2 ^ 59
def prefixEnd_4367817 : Nat := 4983230072969 + 3 ^ 40 * 4367817 * 2
def baseEnd_4367817 : Nat := 2242789531879242629600281

theorem tailTrace_4367817 : CollatzResearch.WordTrace tailWord_4367817 prefixEnd_4367817 2242789531879242629600281 := by
  unfold tailWord_4367817
  simp only [CollatzResearch.WordTrace]
  refine ⟨159307373617152447599501705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106204915744768298399667803 159307373617152447599501705)
  ·
    refine ⟨119480530212864335699626279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159307373617152447599501705 119480530212864335699626279)
    ·
      refine ⟨179220795319296503549439419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119480530212864335699626279 179220795319296503549439419)
      ·
        refine ⟨268831192978944755324159129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179220795319296503549439419 268831192978944755324159129)
        ·
          refine ⟨201623394734208566493119347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268831192978944755324159129 201623394734208566493119347)
          ·
            refine ⟨302435092101312849739679021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201623394734208566493119347 302435092101312849739679021)
            ·
              refine ⟨113413159537992318652379633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302435092101312849739679021 113413159537992318652379633)
              ·
                refine ⟨85059869653494238989284725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113413159537992318652379633 85059869653494238989284725)
                ·
                  refine ⟨7974362780015084905245443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85059869653494238989284725 7974362780015084905245443)
                  ·
                    refine ⟨11961544170022627357868165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7974362780015084905245443 11961544170022627357868165)
                    ·
                      refine ⟨2242789531879242629600281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11961544170022627357868165 2242789531879242629600281)
                      ·
                        rfl

theorem cell23_4367817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_4367817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367817 prefixEnd_4367817 := by exact prefixLift 4367817
  have htrace : WordTrace (prefixWord ++ tailWord_4367817) baseStart_4367817 baseEnd_4367817 := by
    simpa [prefixWord, tailWord_4367817, baseEnd_4367817] using wordTrace_append hprefix tailTrace_4367817
  have hstable : (prefixWord ++ tailWord_4367817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367817).length < 2 ^ (prefixWord ++ tailWord_4367817).sum := by decide
  have hdescent : baseEnd_4367817 < baseStart_4367817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367857 : List Nat := [1, 2, 2, 2, 3, 2, 2, 9]
def baseStart_4367857 : Nat := 118140960795 + 4367857 * 2 ^ 59
def prefixEnd_4367857 : Nat := 4983230072969 + 3 ^ 40 * 4367857 * 2
def baseEnd_4367857 : Nat := 83067039670571202707411

theorem tailTrace_4367857 : CollatzResearch.WordTrace tailWord_4367857 prefixEnd_4367857 83067039670571202707411 := by
  unfold tailWord_4367857
  simp only [CollatzResearch.WordTrace]
  refine ⟨159308832537007534430957825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106205888358005022953971883 159308832537007534430957825)
  ·
    refine ⟨119481624402755650823218369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159308832537007534430957825 119481624402755650823218369)
    ·
      refine ⟨89611218302066738117413777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119481624402755650823218369 89611218302066738117413777)
      ·
        refine ⟨67208413726550053588060333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89611218302066738117413777 67208413726550053588060333)
        ·
          refine ⟨25203155147456270095522625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67208413726550053588060333 25203155147456270095522625)
          ·
            refine ⟨18902366360592202571641969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25203155147456270095522625 18902366360592202571641969)
            ·
              refine ⟨14176774770444151928731477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18902366360592202571641969 14176774770444151928731477)
              ·
                refine ⟨83067039670571202707411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14176774770444151928731477 83067039670571202707411)
                ·
                  rfl

theorem cell23_4367857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 9].length) (baseStart_4367857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367857 prefixEnd_4367857 := by exact prefixLift 4367857
  have htrace : WordTrace (prefixWord ++ tailWord_4367857) baseStart_4367857 baseEnd_4367857 := by
    simpa [prefixWord, tailWord_4367857, baseEnd_4367857] using wordTrace_append hprefix tailTrace_4367857
  have hstable : (prefixWord ++ tailWord_4367857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367857).length < 2 ^ (prefixWord ++ tailWord_4367857).sum := by decide
  have hdescent : baseEnd_4367857 < baseStart_4367857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367861 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4367861 : Nat := 118140960795 + 4367861 * 2 ^ 59
def prefixEnd_4367861 : Nat := 4983230072969 + 3 ^ 40 * 4367861 * 2
def baseEnd_4367861 : Nat := 747604041676013485816693

theorem tailTrace_4367861 : CollatzResearch.WordTrace tailWord_4367861 prefixEnd_4367861 747604041676013485816693 := by
  unfold tailWord_4367861
  simp only [CollatzResearch.WordTrace]
  refine ⟨159308978428993043114103437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106205985619328695409402291 159308978428993043114103437)
  ·
    refine ⟨59740866910872391167788789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159308978428993043114103437 59740866910872391167788789)
    ·
      refine ⟨5600706272894286671980199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59740866910872391167788789 5600706272894286671980199)
      ·
        refine ⟨8401059409341430007970299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600706272894286671980199 8401059409341430007970299)
        ·
          refine ⟨12601589114012145011955449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401059409341430007970299 12601589114012145011955449)
          ·
            refine ⟨9451191835509108758966587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12601589114012145011955449 9451191835509108758966587)
            ·
              refine ⟨14176787753263663138449881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451191835509108758966587 14176787753263663138449881)
              ·
                refine ⟨10632590814947747353837411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14176787753263663138449881 10632590814947747353837411)
                ·
                  refine ⟨15948886222421621030756117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10632590814947747353837411 15948886222421621030756117)
                  ·
                    refine ⟨747604041676013485816693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15948886222421621030756117 747604041676013485816693)
                    ·
                      rfl

theorem cell23_4367861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4367861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367861 prefixEnd_4367861 := by exact prefixLift 4367861
  have htrace : WordTrace (prefixWord ++ tailWord_4367861) baseStart_4367861 baseEnd_4367861 := by
    simpa [prefixWord, tailWord_4367861, baseEnd_4367861] using wordTrace_append hprefix tailTrace_4367861
  have hstable : (prefixWord ++ tailWord_4367861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367861).length < 2 ^ (prefixWord ++ tailWord_4367861).sum := by decide
  have hdescent : baseEnd_4367861 < baseStart_4367861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367864 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_4367864 : Nat := 118140960795 + 4367864 * 2 ^ 59
def prefixEnd_4367864 : Nat := 4983230072969 + 3 ^ 40 * 4367864 * 2
def baseEnd_4367864 : Nat := 2242813665470003945712565

theorem tailTrace_4367864 : CollatzResearch.WordTrace tailWord_4367864 prefixEnd_4367864 2242813665470003945712565 := by
  unfold tailWord_4367864
  simp only [CollatzResearch.WordTrace]
  refine ⟨79654543923991087313231323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106206058565321449750975097 79654543923991087313231323)
  ·
    refine ⟨119481815885986630969846985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79654543923991087313231323 119481815885986630969846985)
    ·
      refine ⟨89611361914489973227385239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119481815885986630969846985 89611361914489973227385239)
      ·
        refine ⟨134417042871734959841077859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89611361914489973227385239 134417042871734959841077859)
        ·
          refine ⟨201625564307602439761616789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134417042871734959841077859 201625564307602439761616789)
          ·
            refine ⟨9451198326918864363825787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 201625564307602439761616789 9451198326918864363825787)
            ·
              refine ⟨14176797490378296545738681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451198326918864363825787 14176797490378296545738681)
              ·
                refine ⟨10632598117783722409304011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14176797490378296545738681 10632598117783722409304011)
                ·
                  refine ⟨15948897176675583613956017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10632598117783722409304011 15948897176675583613956017)
                  ·
                    refine ⟨11961672882506687710467013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15948897176675583613956017 11961672882506687710467013)
                    ·
                      refine ⟨2242813665470003945712565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11961672882506687710467013 2242813665470003945712565)
                      ·
                        rfl

theorem cell23_4367864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_4367864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367864 prefixEnd_4367864 := by exact prefixLift 4367864
  have htrace : WordTrace (prefixWord ++ tailWord_4367864) baseStart_4367864 baseEnd_4367864 := by
    simpa [prefixWord, tailWord_4367864, baseEnd_4367864] using wordTrace_append hprefix tailTrace_4367864
  have hstable : (prefixWord ++ tailWord_4367864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367864).length < 2 ^ (prefixWord ++ tailWord_4367864).sum := by decide
  have hdescent : baseEnd_4367864 < baseStart_4367864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367874 : List Nat := [3, 4, 1, 2, 1, 12]
def baseStart_4367874 : Nat := 118140960795 + 4367874 * 2 ^ 59
def prefixEnd_4367874 : Nat := 4983230072969 + 3 ^ 40 * 4367874 * 2
def baseEnd_4367874 : Nat := 9229706997022835006533

theorem tailTrace_4367874 : CollatzResearch.WordTrace tailWord_4367874 prefixEnd_4367874 9229706997022835006533 := by
  unfold tailWord_4367874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39827363144486486583581669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106206301718630630889551117 39827363144486486583581669)
  ·
    refine ⟨7467630589591216234421563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39827363144486486583581669 7467630589591216234421563)
    ·
      refine ⟨11201445884386824351632345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7467630589591216234421563 11201445884386824351632345)
      ·
        refine ⟨8401084413290118263724259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11201445884386824351632345 8401084413290118263724259)
        ·
          refine ⟨12601626619935177395586389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401084413290118263724259 12601626619935177395586389)
          ·
            refine ⟨9229706997022835006533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12601626619935177395586389 9229706997022835006533)
            ·
              rfl

theorem cell23_4367874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 12].length) (baseStart_4367874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367874 prefixEnd_4367874 := by exact prefixLift 4367874
  have htrace : WordTrace (prefixWord ++ tailWord_4367874) baseStart_4367874 baseEnd_4367874 := by
    simpa [prefixWord, tailWord_4367874, baseEnd_4367874] using wordTrace_append hprefix tailTrace_4367874
  have hstable : (prefixWord ++ tailWord_4367874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367874).length < 2 ^ (prefixWord ++ tailWord_4367874).sum := by decide
  have hdescent : baseEnd_4367874 < baseStart_4367874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367901 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_4367901 : Nat := 118140960795 + 4367901 * 2 ^ 59
def prefixEnd_4367901 : Nat := 4983230072969 + 3 ^ 40 * 4367901 * 2
def baseEnd_4367901 : Nat := 2242832664254220300949895

theorem tailTrace_4367901 : CollatzResearch.WordTrace tailWord_4367901 prefixEnd_4367901 2242832664254220300949895 := by
  unfold tailWord_4367901
  simp only [CollatzResearch.WordTrace]
  refine ⟨159310437348848129945559557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106206958232565419963706371 159310437348848129945559557)
  ·
    refine ⟨29870707002909024364792417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159310437348848129945559557 29870707002909024364792417)
    ·
      refine ⟨22403030252181768273594313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29870707002909024364792417 22403030252181768273594313)
      ·
        refine ⟨16802272689136326205195735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22403030252181768273594313 16802272689136326205195735)
        ·
          refine ⟨25203409033704489307793603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16802272689136326205195735 25203409033704489307793603)
          ·
            refine ⟨37805113550556733961690405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25203409033704489307793603 37805113550556733961690405)
            ·
              refine ⟨7088458790729387617816951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37805113550556733961690405 7088458790729387617816951)
              ·
                refine ⟨10632688186094081426725427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088458790729387617816951 10632688186094081426725427)
                ·
                  refine ⟨15949032279141122140088141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10632688186094081426725427 15949032279141122140088141)
                  ·
                    refine ⟨5980887104677920802533053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15949032279141122140088141 5980887104677920802533053)
                    ·
                      refine ⟨2242832664254220300949895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5980887104677920802533053 2242832664254220300949895)
                      ·
                        rfl

theorem cell23_4367901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_4367901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367901 prefixEnd_4367901 := by exact prefixLift 4367901
  have htrace : WordTrace (prefixWord ++ tailWord_4367901) baseStart_4367901 baseEnd_4367901 := by
    simpa [prefixWord, tailWord_4367901, baseEnd_4367901] using wordTrace_append hprefix tailTrace_4367901
  have hstable : (prefixWord ++ tailWord_4367901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367901).length < 2 ^ (prefixWord ++ tailWord_4367901).sum := by decide
  have hdescent : baseEnd_4367901 < baseStart_4367901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367914 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4367914 : Nat := 118140960795 + 4367914 * 2 ^ 59
def prefixEnd_4367914 : Nat := 4983230072969 + 3 ^ 40 * 4367914 * 2
def baseEnd_4367914 : Nat := 2242839339502728750087335

theorem tailTrace_4367914 : CollatzResearch.WordTrace tailWord_4367914 prefixEnd_4367914 2242839339502728750087335 := by
  unfold tailWord_4367914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39827727874450258291445699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106207274331867355443855197 39827727874450258291445699)
  ·
    refine ⟨59741591811675387437168549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39827727874450258291445699 59741591811675387437168549)
    ·
      refine ⟨11201548464689135144469103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59741591811675387437168549 11201548464689135144469103)
      ·
        refine ⟨16802322697033702716703655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11201548464689135144469103 16802322697033702716703655)
        ·
          refine ⟨25203484045550554075055483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16802322697033702716703655 25203484045550554075055483)
          ·
            refine ⟨37805226068325831112583225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25203484045550554075055483 37805226068325831112583225)
            ·
              refine ⟨28353919551244373334437419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37805226068325831112583225 28353919551244373334437419)
              ·
                refine ⟨42530879326866560001656129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28353919551244373334437419 42530879326866560001656129)
                ·
                  refine ⟨31898159495149920001242097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42530879326866560001656129 31898159495149920001242097)
                  ·
                    refine ⟨23923619621362440000931573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31898159495149920001242097 23923619621362440000931573)
                    ·
                      refine ⟨2242839339502728750087335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23923619621362440000931573 2242839339502728750087335)
                      ·
                        rfl

theorem cell23_4367914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4367914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367914 prefixEnd_4367914 := by exact prefixLift 4367914
  have htrace : WordTrace (prefixWord ++ tailWord_4367914) baseStart_4367914 baseEnd_4367914 := by
    simpa [prefixWord, tailWord_4367914, baseEnd_4367914] using wordTrace_append hprefix tailTrace_4367914
  have hstable : (prefixWord ++ tailWord_4367914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367914).length < 2 ^ (prefixWord ++ tailWord_4367914).sum := by decide
  have hdescent : baseEnd_4367914 < baseStart_4367914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4367928 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_4367928 : Nat := 118140960795 + 4367928 * 2 ^ 59
def prefixEnd_4367928 : Nat := 4983230072969 + 3 ^ 40 * 4367928 * 2
def baseEnd_4367928 : Nat := 2242846528231891695312271

theorem tailTrace_4367928 : CollatzResearch.WordTrace tailWord_4367928 prefixEnd_4367928 2242846528231891695312271 := by
  unfold tailWord_4367928
  simp only [CollatzResearch.WordTrace]
  refine ⟨79655711059875156778396219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106207614746500209037861625 79655711059875156778396219)
  ·
    refine ⟨119483566589812735167594329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79655711059875156778396219 119483566589812735167594329)
    ·
      refine ⟨89612674942359551375695747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119483566589812735167594329 89612674942359551375695747)
      ·
        refine ⟨134419012413539327063543621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89612674942359551375695747 134419012413539327063543621)
        ·
          refine ⟨25203564827538623824414429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134419012413539327063543621 25203564827538623824414429)
          ·
            refine ⟨9451336810326983934155411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25203564827538623824414429 9451336810326983934155411)
            ·
              refine ⟨14177005215490475901233117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451336810326983934155411 14177005215490475901233117)
              ·
                refine ⟨5316376955808928462962419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14177005215490475901233117 5316376955808928462962419)
                ·
                  refine ⟨7974565433713392694443629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5316376955808928462962419 7974565433713392694443629)
                  ·
                    refine ⟨2990462037642522260416361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7974565433713392694443629 2990462037642522260416361)
                    ·
                      refine ⟨2242846528231891695312271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990462037642522260416361 2242846528231891695312271)
                      ·
                        rfl

theorem cell23_4367928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_4367928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4367928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4367928 prefixEnd_4367928 := by exact prefixLift 4367928
  have htrace : WordTrace (prefixWord ++ tailWord_4367928) baseStart_4367928 baseEnd_4367928 := by
    simpa [prefixWord, tailWord_4367928, baseEnd_4367928] using wordTrace_append hprefix tailTrace_4367928
  have hstable : (prefixWord ++ tailWord_4367928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4367928).length < 2 ^ (prefixWord ++ tailWord_4367928).sum := by decide
  have hdescent : baseEnd_4367928 < baseStart_4367928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4367928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368028 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_4368028 : Nat := 118140960795 + 4368028 * 2 ^ 59
def prefixEnd_4368028 : Nat := 4983230072969 + 3 ^ 40 * 4368028 * 2
def baseEnd_4368028 : Nat := 747632625432447101353937

theorem tailTrace_4368028 : CollatzResearch.WordTrace tailWord_4368028 prefixEnd_4368028 747632625432447101353937 := by
  unfold tailWord_4368028
  simp only [CollatzResearch.WordTrace]
  refine ⟨79657534709694015317716369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106210046279592020423621825 79657534709694015317716369)
  ·
    refine ⟨59743151032270511488287277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79657534709694015317716369 59743151032270511488287277)
    ·
      refine ⟨22403681637101441808107729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59743151032270511488287277 22403681637101441808107729)
      ·
        refine ⟨16802761227826081356080797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22403681637101441808107729 16802761227826081356080797)
        ·
          refine ⟨6301035460434780508530299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16802761227826081356080797 6301035460434780508530299)
          ·
            refine ⟨9451553190652170762795449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301035460434780508530299 9451553190652170762795449)
            ·
              refine ⟨7088664892989128072096587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9451553190652170762795449 7088664892989128072096587)
              ·
                refine ⟨10632997339483692108144881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088664892989128072096587 10632997339483692108144881)
                ·
                  refine ⟨7974748004612769081108661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10632997339483692108144881 7974748004612769081108661)
                  ·
                    refine ⟨747632625432447101353937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7974748004612769081108661 747632625432447101353937)
                    ·
                      rfl

theorem cell23_4368028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_4368028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368028 prefixEnd_4368028 := by exact prefixLift 4368028
  have htrace : WordTrace (prefixWord ++ tailWord_4368028) baseStart_4368028 baseEnd_4368028 := by
    simpa [prefixWord, tailWord_4368028, baseEnd_4368028] using wordTrace_append hprefix tailTrace_4368028
  have hstable : (prefixWord ++ tailWord_4368028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368028).length < 2 ^ (prefixWord ++ tailWord_4368028).sum := by decide
  have hdescent : baseEnd_4368028 < baseStart_4368028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368051 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3]
def baseStart_4368051 : Nat := 118140960795 + 4368051 * 2 ^ 59
def prefixEnd_4368051 : Nat := 4983230072969 + 3 ^ 40 * 4368051 * 2
def baseEnd_4368051 : Nat := 2242909686352394714074205

theorem tailTrace_4368051 : CollatzResearch.WordTrace tailWord_4368051 prefixEnd_4368051 2242909686352394714074205 := by
  unfold tailWord_4368051
  simp only [CollatzResearch.WordTrace]
  refine ⟨159315908298304705563520007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106210605532203137042346671 159315908298304705563520007)
  ·
    refine ⟨238973862447457058345280011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159315908298304705563520007 238973862447457058345280011)
    ·
      refine ⟨358460793671185587517920017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238973862447457058345280011 358460793671185587517920017)
      ·
        refine ⟨268845595253389190638440013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358460793671185587517920017 268845595253389190638440013)
        ·
          refine ⟨100817098220020946489415005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268845595253389190638440013 100817098220020946489415005)
          ·
            refine ⟨37806411832507854933530627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100817098220020946489415005 37806411832507854933530627)
            ·
              refine ⟨56709617748761782400295941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37806411832507854933530627 56709617748761782400295941)
              ·
                refine ⟨10633053327892834200055489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56709617748761782400295941 10633053327892834200055489)
                ·
                  refine ⟨7974789995919625650041617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10633053327892834200055489 7974789995919625650041617)
                  ·
                    refine ⟨5981092496939719237531213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7974789995919625650041617 5981092496939719237531213)
                    ·
                      refine ⟨2242909686352394714074205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981092496939719237531213 2242909686352394714074205)
                      ·
                        rfl

theorem cell23_4368051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_4368051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368051 prefixEnd_4368051 := by exact prefixLift 4368051
  have htrace : WordTrace (prefixWord ++ tailWord_4368051) baseStart_4368051 baseEnd_4368051 := by
    simpa [prefixWord, tailWord_4368051, baseEnd_4368051] using wordTrace_append hprefix tailTrace_4368051
  have hstable : (prefixWord ++ tailWord_4368051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368051).length < 2 ^ (prefixWord ++ tailWord_4368051).sum := by decide
  have hdescent : baseEnd_4368051 < baseStart_4368051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368108 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_4368108 : Nat := 118140960795 + 4368108 * 2 ^ 59
def prefixEnd_4368108 : Nat := 4983230072969 + 3 ^ 40 * 4368108 * 2
def baseEnd_4368108 : Nat := 2242938954749700991061443

theorem tailTrace_4368108 : CollatzResearch.WordTrace tailWord_4368108 prefixEnd_4368108 2242938954749700991061443 := by
  unfold tailWord_4368108
  simp only [CollatzResearch.WordTrace]
  refine ⟨79658993629549102149172489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106211991506065469532229985 79658993629549102149172489)
  ·
    refine ⟨59744245222161826611879367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79658993629549102149172489 59744245222161826611879367)
    ·
      refine ⟨89616367833242739917819051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59744245222161826611879367 89616367833242739917819051)
      ·
        refine ⟨134424551749864109876728577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89616367833242739917819051 134424551749864109876728577)
        ·
          refine ⟨100818413812398082407546433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134424551749864109876728577 100818413812398082407546433)
          ·
            refine ⟨75613810359298561805659825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100818413812398082407546433 75613810359298561805659825)
            ·
              refine ⟨56710357769473921354244869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75613810359298561805659825 56710357769473921354244869)
              ·
                refine ⟨10633192081776360253920913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56710357769473921354244869 10633192081776360253920913)
                ·
                  refine ⟨7974894061332270190440685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10633192081776360253920913 7974894061332270190440685)
                  ·
                    refine ⟨2990585272999601321415257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7974894061332270190440685 2990585272999601321415257)
                    ·
                      refine ⟨2242938954749700991061443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990585272999601321415257 2242938954749700991061443)
                      ·
                        rfl

theorem cell23_4368108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_4368108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368108 prefixEnd_4368108 := by exact prefixLift 4368108
  have htrace : WordTrace (prefixWord ++ tailWord_4368108) baseStart_4368108 baseEnd_4368108 := by
    simpa [prefixWord, tailWord_4368108, baseEnd_4368108] using wordTrace_append hprefix tailTrace_4368108
  have hstable : (prefixWord ++ tailWord_4368108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368108).length < 2 ^ (prefixWord ++ tailWord_4368108).sum := by decide
  have hdescent : baseEnd_4368108 < baseStart_4368108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368115 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 1, 1, 3]
def baseStart_4368115 : Nat := 118140960795 + 4368115 * 2 ^ 59
def prefixEnd_4368115 : Nat := 4983230072969 + 3 ^ 40 * 4368115 * 2
def baseEnd_4368115 : Nat := 2242942549114282463673911

theorem tailTrace_4368115 : CollatzResearch.WordTrace tailWord_4368115 prefixEnd_4368115 2242942549114282463673911 := by
  unfold tailWord_4368115
  simp only [CollatzResearch.WordTrace]
  refine ⟨159318242570072844493849799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106212161713381896329233199 159318242570072844493849799)
  ·
    refine ⟨238977363855109266740774699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159318242570072844493849799 238977363855109266740774699)
    ·
      refine ⟨358466045782663900111162049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238977363855109266740774699 358466045782663900111162049)
      ·
        refine ⟨268849534336997925083371537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358466045782663900111162049 268849534336997925083371537)
        ·
          refine ⟨201637150752748443812528653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268849534336997925083371537 201637150752748443812528653)
          ·
            refine ⟨75613931532280666429698245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201637150752748443812528653 75613931532280666429698245)
            ·
              refine ⟨14177612162302624955568421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75613931532280666429698245 14177612162302624955568421)
              ·
                refine ⟨2658302280431742179169079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14177612162302624955568421 2658302280431742179169079)
                ·
                  refine ⟨3987453420647613268753619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2658302280431742179169079 3987453420647613268753619)
                  ·
                    refine ⟨5981180130971419903130429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3987453420647613268753619 5981180130971419903130429)
                    ·
                      refine ⟨2242942549114282463673911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981180130971419903130429 2242942549114282463673911)
                      ·
                        rfl

theorem cell23_4368115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 1, 1, 3].length) (baseStart_4368115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368115 prefixEnd_4368115 := by exact prefixLift 4368115
  have htrace : WordTrace (prefixWord ++ tailWord_4368115) baseStart_4368115 baseEnd_4368115 := by
    simpa [prefixWord, tailWord_4368115, baseEnd_4368115] using wordTrace_append hprefix tailTrace_4368115
  have hstable : (prefixWord ++ tailWord_4368115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368115).length < 2 ^ (prefixWord ++ tailWord_4368115).sum := by decide
  have hdescent : baseEnd_4368115 < baseStart_4368115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368131 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 1, 6]
def baseStart_4368131 : Nat := 118140960795 + 4368131 * 2 ^ 59
def prefixEnd_4368131 : Nat := 4983230072969 + 3 ^ 40 * 4368131 * 2
def baseEnd_4368131 : Nat := 747650254934918133691279

theorem tailTrace_4368131 : CollatzResearch.WordTrace tailWord_4368131 prefixEnd_4368131 747650254934918133691279 := by
  unfold tailWord_4368131
  simp only [CollatzResearch.WordTrace]
  refine ⟨159318826138014879226432247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106212550758676586150954831 159318826138014879226432247)
  ·
    refine ⟨238978239207022318839648371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159318826138014879226432247 238978239207022318839648371)
    ·
      refine ⟨358467358810533478259472557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238978239207022318839648371 358467358810533478259472557)
      ·
        refine ⟨134425259553950054347302209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358467358810533478259472557 134425259553950054347302209)
        ·
          refine ⟨100818944665462540760476657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134425259553950054347302209 100818944665462540760476657)
          ·
            refine ⟨75614208499096905570357493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100818944665462540760476657 75614208499096905570357493)
            ·
              refine ⟨7088832046790334897221015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75614208499096905570357493 7088832046790334897221015)
              ·
                refine ⟨10633248070185502345831523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088832046790334897221015 10633248070185502345831523)
                ·
                  refine ⟨15949872105278253518747285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10633248070185502345831523 15949872105278253518747285)
                  ·
                    refine ⟨747650254934918133691279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15949872105278253518747285 747650254934918133691279)
                    ·
                      rfl

theorem cell23_4368131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 6].length) (baseStart_4368131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368131 prefixEnd_4368131 := by exact prefixLift 4368131
  have htrace : WordTrace (prefixWord ++ tailWord_4368131) baseStart_4368131 baseEnd_4368131 := by
    simpa [prefixWord, tailWord_4368131, baseEnd_4368131] using wordTrace_append hprefix tailTrace_4368131
  have hstable : (prefixWord ++ tailWord_4368131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368131).length < 2 ^ (prefixWord ++ tailWord_4368131).sum := by decide
  have hdescent : baseEnd_4368131 < baseStart_4368131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368135 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 1, 5]
def baseStart_4368135 : Nat := 118140960795 + 4368135 * 2 ^ 59
def prefixEnd_4368135 : Nat := 4983230072969 + 3 ^ 40 * 4368135 * 2
def baseEnd_4368135 : Nat := 747650939575790795141273

theorem tailTrace_4368135 : CollatzResearch.WordTrace tailWord_4368135 prefixEnd_4368135 747650939575790795141273 := by
  unfold tailWord_4368135
  simp only [CollatzResearch.WordTrace]
  refine ⟨159318972030000387909577859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106212648020000258606385239 159318972030000387909577859)
  ·
    refine ⟨238978458045000581864366789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159318972030000387909577859 238978458045000581864366789)
    ·
      refine ⟨44808460883437609099568773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238978458045000581864366789 44808460883437609099568773)
      ·
        refine ⟨8401586415644551706169145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44808460883437609099568773 8401586415644551706169145)
        ·
          refine ⟨6301189811733413779626859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401586415644551706169145 6301189811733413779626859)
          ·
            refine ⟨9451784717600120669440289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301189811733413779626859 9451784717600120669440289)
            ·
              refine ⟨7088838538200090502080217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9451784717600120669440289 7088838538200090502080217)
              ·
                refine ⟨5316628903650067876560163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7088838538200090502080217 5316628903650067876560163)
                ·
                  refine ⟨7974943355475101814840245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5316628903650067876560163 7974943355475101814840245)
                  ·
                    refine ⟨747650939575790795141273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7974943355475101814840245 747650939575790795141273)
                    ·
                      rfl

theorem cell23_4368135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_4368135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368135 prefixEnd_4368135 := by exact prefixLift 4368135
  have htrace : WordTrace (prefixWord ++ tailWord_4368135) baseStart_4368135 baseEnd_4368135 := by
    simpa [prefixWord, tailWord_4368135, baseEnd_4368135] using wordTrace_append hprefix tailTrace_4368135
  have hstable : (prefixWord ++ tailWord_4368135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368135).length < 2 ^ (prefixWord ++ tailWord_4368135).sum := by decide
  have hdescent : baseEnd_4368135 < baseStart_4368135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368138 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_4368138 : Nat := 118140960795 + 4368138 * 2 ^ 59
def prefixEnd_4368138 : Nat := 4983230072969 + 3 ^ 40 * 4368138 * 2
def baseEnd_4368138 : Nat := 2242954359169335873686305

theorem tailTrace_4368138 : CollatzResearch.WordTrace tailWord_4368138 prefixEnd_4368138 2242954359169335873686305 := by
  unfold tailWord_4368138
  simp only [CollatzResearch.WordTrace]
  refine ⟨39829770362247379855484267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106212720965993012947958045 39829770362247379855484267)
  ·
    refine ⟨59744655543371069783226401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39829770362247379855484267 59744655543371069783226401)
    ·
      refine ⟨44808491657528302337419801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59744655543371069783226401 44808491657528302337419801)
      ·
        refine ⟨33606368743146226753064851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44808491657528302337419801 33606368743146226753064851)
        ·
          refine ⟨50409553114719340129597277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33606368743146226753064851 50409553114719340129597277)
          ·
            refine ⟨18903582418019752548598979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50409553114719340129597277 18903582418019752548598979)
            ·
              refine ⟨28355373627029628822898469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18903582418019752548598979 28355373627029628822898469)
              ·
                refine ⟨5316632555068055404293463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28355373627029628822898469 5316632555068055404293463)
                ·
                  refine ⟨7974948832602083106440195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5316632555068055404293463 7974948832602083106440195)
                  ·
                    refine ⟨11962423248903124659660293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7974948832602083106440195 11962423248903124659660293)
                    ·
                      refine ⟨2242954359169335873686305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11962423248903124659660293 2242954359169335873686305)
                      ·
                        rfl

theorem cell23_4368138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_4368138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368138 prefixEnd_4368138 := by exact prefixLift 4368138
  have htrace : WordTrace (prefixWord ++ tailWord_4368138) baseStart_4368138 baseEnd_4368138 := by
    simpa [prefixWord, tailWord_4368138, baseEnd_4368138] using wordTrace_append hprefix tailTrace_4368138
  have hstable : (prefixWord ++ tailWord_4368138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368138).length < 2 ^ (prefixWord ++ tailWord_4368138).sum := by decide
  have hdescent : baseEnd_4368138 < baseStart_4368138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368161 : List Nat := [1, 2, 3, 2, 1, 5, 9]
def baseStart_4368161 : Nat := 118140960795 + 4368161 * 2 ^ 59
def prefixEnd_4368161 : Nat := 4983230072969 + 3 ^ 40 * 4368161 * 2
def baseEnd_4368161 : Nat := 27690940360794929428379

theorem tailTrace_4368161 : CollatzResearch.WordTrace tailWord_4368161 prefixEnd_4368161 27690940360794929428379 := by
  unfold tailWord_4368161
  simp only [CollatzResearch.WordTrace]
  refine ⟨159319920327906194350024337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106213280218604129566682891 159319920327906194350024337)
  ·
    refine ⟨119489940245929645762518253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159319920327906194350024337 119489940245929645762518253)
    ·
      refine ⟨44808727592223617160944345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119489940245929645762518253 44808727592223617160944345)
      ·
        refine ⟨33606545694167712870708259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44808727592223617160944345 33606545694167712870708259)
        ·
          refine ⟨50409818541251569306062389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33606545694167712870708259 50409818541251569306062389)
          ·
            refine ⟨4725920488242334622443349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50409818541251569306062389 4725920488242334622443349)
            ·
              refine ⟨27690940360794929428379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4725920488242334622443349 27690940360794929428379)
              ·
                rfl

theorem cell23_4368161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 9].length) (baseStart_4368161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368161 prefixEnd_4368161 := by exact prefixLift 4368161
  have htrace : WordTrace (prefixWord ++ tailWord_4368161) baseStart_4368161 baseEnd_4368161 := by
    simpa [prefixWord, tailWord_4368161, baseEnd_4368161] using wordTrace_append hprefix tailTrace_4368161
  have hstable : (prefixWord ++ tailWord_4368161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368161).length < 2 ^ (prefixWord ++ tailWord_4368161).sum := by decide
  have hdescent : baseEnd_4368161 < baseStart_4368161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368172 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_4368172 : Nat := 118140960795 + 4368172 * 2 ^ 59
def prefixEnd_4368172 : Nat := 4983230072969 + 3 ^ 40 * 4368172 * 2
def baseEnd_4368172 : Nat := 2242971817511588740661149

theorem tailTrace_4368172 : CollatzResearch.WordTrace tailWord_4368172 prefixEnd_4368172 2242971817511588740661149 := by
  unfold tailWord_4368172
  simp only [CollatzResearch.WordTrace]
  refine ⟨79660160765433171614337385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106213547687244228819116513 79660160765433171614337385)
  ·
    refine ⟨59745120574074878710753039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79660160765433171614337385 59745120574074878710753039)
    ·
      refine ⟨89617680861112318066129559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59745120574074878710753039 89617680861112318066129559)
      ·
        refine ⟨134426521291668477099194339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89617680861112318066129559 134426521291668477099194339)
        ·
          refine ⟨201639781937502715648791509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134426521291668477099194339 201639781937502715648791509)
          ·
            refine ⟨4725932389160219898018551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 201639781937502715648791509 4725932389160219898018551)
            ·
              refine ⟨7088898583740329847027827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725932389160219898018551 7088898583740329847027827)
              ·
                refine ⟨10633347875610494770541741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088898583740329847027827 10633347875610494770541741)
                ·
                  refine ⟨3987505453353935538953153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10633347875610494770541741 3987505453353935538953153)
                  ·
                    refine ⟨2990629090015451654214865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3987505453353935538953153 2990629090015451654214865)
                    ·
                      refine ⟨2242971817511588740661149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990629090015451654214865 2242971817511588740661149)
                      ·
                        rfl

theorem cell23_4368172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_4368172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368172 prefixEnd_4368172 := by exact prefixLift 4368172
  have htrace : WordTrace (prefixWord ++ tailWord_4368172) baseStart_4368172 baseEnd_4368172 := by
    simpa [prefixWord, tailWord_4368172, baseEnd_4368172] using wordTrace_append hprefix tailTrace_4368172
  have hstable : (prefixWord ++ tailWord_4368172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368172).length < 2 ^ (prefixWord ++ tailWord_4368172).sum := by decide
  have hdescent : baseEnd_4368172 < baseStart_4368172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368182 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4368182 : Nat := 118140960795 + 4368182 * 2 ^ 59
def prefixEnd_4368182 : Nat := 4983230072969 + 3 ^ 40 * 4368182 * 2
def baseEnd_4368182 : Nat := 747658984106044567178701

theorem tailTrace_4368182 : CollatzResearch.WordTrace tailWord_4368182 prefixEnd_4368182 747658984106044567178701 := by
  unfold tailWord_4368182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957542891301882183533675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106213790840553409957692533 9957542891301882183533675)
  ·
    refine ⟨14936314336952823275300513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9957542891301882183533675 14936314336952823275300513)
    ·
      refine ⟨11202235752714617456475385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14936314336952823275300513 11202235752714617456475385)
      ·
        refine ⟨8401676814535963092356539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11202235752714617456475385 8401676814535963092356539)
        ·
          refine ⟨12602515221803944638534809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401676814535963092356539 12602515221803944638534809)
          ·
            refine ⟨9451886416352958478901107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12602515221803944638534809 9451886416352958478901107)
            ·
              refine ⟨14177829624529437718351661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451886416352958478901107 14177829624529437718351661)
              ·
                refine ⟨5316686109198539144381873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14177829624529437718351661 5316686109198539144381873)
                ·
                  refine ⟨3987514581898904358286405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5316686109198539144381873 3987514581898904358286405)
                  ·
                    refine ⟨747658984106044567178701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3987514581898904358286405 747658984106044567178701)
                    ·
                      rfl

theorem cell23_4368182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4368182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368182 prefixEnd_4368182 := by exact prefixLift 4368182
  have htrace : WordTrace (prefixWord ++ tailWord_4368182) baseStart_4368182 baseEnd_4368182 := by
    simpa [prefixWord, tailWord_4368182, baseEnd_4368182] using wordTrace_append hprefix tailTrace_4368182
  have hstable : (prefixWord ++ tailWord_4368182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368182).length < 2 ^ (prefixWord ++ tailWord_4368182).sum := by decide
  have hdescent : baseEnd_4368182 < baseStart_4368182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368205 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4368205 : Nat := 118140960795 + 4368205 * 2 ^ 59
def prefixEnd_4368205 : Nat := 4983230072969 + 3 ^ 40 * 4368205 * 2
def baseEnd_4368205 : Nat := 2242988762373187111548497

theorem tailTrace_4368205 : CollatzResearch.WordTrace tailWord_4368205 prefixEnd_4368205 2242988762373187111548497 := by
  unfold tailWord_4368205
  simp only [CollatzResearch.WordTrace]
  refine ⟨159321525139746789864626069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106214350093164526576417379 159321525139746789864626069)
  ·
    refine ⟨7468196490925630774904347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159321525139746789864626069 7468196490925630774904347)
    ·
      refine ⟨11202294736388446162356521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468196490925630774904347 11202294736388446162356521)
      ·
        refine ⟨8401721052291334621767391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11202294736388446162356521 8401721052291334621767391)
        ·
          refine ⟨12602581578437001932651087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401721052291334621767391 12602581578437001932651087)
          ·
            refine ⟨18903872367655502898976631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602581578437001932651087 18903872367655502898976631)
            ·
              refine ⟨28355808551483254348464947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18903872367655502898976631 28355808551483254348464947)
              ·
                refine ⟨42533712827224881522697421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28355808551483254348464947 42533712827224881522697421)
                ·
                  refine ⟨15950142310209330571011533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42533712827224881522697421 15950142310209330571011533)
                  ·
                    refine ⟨5981303366328498964129325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15950142310209330571011533 5981303366328498964129325)
                    ·
                      refine ⟨2242988762373187111548497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981303366328498964129325 2242988762373187111548497)
                      ·
                        rfl

theorem cell23_4368205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4368205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368205 prefixEnd_4368205 := by exact prefixLift 4368205
  have htrace : WordTrace (prefixWord ++ tailWord_4368205) baseStart_4368205 baseEnd_4368205 := by
    simpa [prefixWord, tailWord_4368205, baseEnd_4368205] using wordTrace_append hprefix tailTrace_4368205
  have hstable : (prefixWord ++ tailWord_4368205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368205).length < 2 ^ (prefixWord ++ tailWord_4368205).sum := by decide
  have hdescent : baseEnd_4368205 < baseStart_4368205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368238 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_4368238 : Nat := 118140960795 + 4368238 * 2 ^ 59
def prefixEnd_4368238 : Nat := 4983230072969 + 3 ^ 40 * 4368238 * 2
def baseEnd_4368238 : Nat := 747668569078261827478615

theorem tailTrace_4368238 : CollatzResearch.WordTrace tailWord_4368238 prefixEnd_4368238 747668569078261827478615 := by
  unfold tailWord_4368238
  simp only [CollatzResearch.WordTrace]
  refine ⟨19915341093578404562572171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106215152499084824333718245 19915341093578404562572171)
  ·
    refine ⟨29873011640367606843858257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19915341093578404562572171 29873011640367606843858257)
    ·
      refine ⟨22404758730275705132893693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29873011640367606843858257 22404758730275705132893693)
      ·
        refine ⟨8401784523853389424835135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22404758730275705132893693 8401784523853389424835135)
        ·
          refine ⟨12602676785780084137252703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401784523853389424835135 12602676785780084137252703)
          ·
            refine ⟨18904015178670126205879055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602676785780084137252703 18904015178670126205879055)
            ·
              refine ⟨28356022768005189308818583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18904015178670126205879055 28356022768005189308818583)
              ·
                refine ⟨42534034152007783963227875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28356022768005189308818583 42534034152007783963227875)
                ·
                  refine ⟨63801051228011675944841813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42534034152007783963227875 63801051228011675944841813)
                  ·
                    refine ⟨747668569078261827478615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63801051228011675944841813 747668569078261827478615)
                    ·
                      rfl

theorem cell23_4368238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_4368238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368238 prefixEnd_4368238 := by exact prefixLift 4368238
  have htrace : WordTrace (prefixWord ++ tailWord_4368238) baseStart_4368238 baseEnd_4368238 := by
    simpa [prefixWord, tailWord_4368238, baseEnd_4368238] using wordTrace_append hprefix tailTrace_4368238
  have hstable : (prefixWord ++ tailWord_4368238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368238).length < 2 ^ (prefixWord ++ tailWord_4368238).sum := by decide
  have hdescent : baseEnd_4368238 < baseStart_4368238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368266 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4368266 : Nat := 118140960795 + 4368266 * 2 ^ 59
def prefixEnd_4368266 : Nat := 4983230072969 + 3 ^ 40 * 4368266 * 2
def baseEnd_4368266 : Nat := 2243020084693111372885717

theorem tailTrace_4368266 : CollatzResearch.WordTrace tailWord_4368266 prefixEnd_4368266 2243020084693111372885717 := by
  unfold tailWord_4368266
  simp only [CollatzResearch.WordTrace]
  refine ⟨39830937498131449320649163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106215833328350531521731101 39830937498131449320649163)
  ·
    refine ⟨59746406247197173980973745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39830937498131449320649163 59746406247197173980973745)
    ·
      refine ⟨44809804685397880485730309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59746406247197173980973745 44809804685397880485730309)
      ·
        refine ⟨8401838378512102591074433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44809804685397880485730309 8401838378512102591074433)
        ·
          refine ⟨6301378783884076943305825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401838378512102591074433 6301378783884076943305825)
          ·
            refine ⟨4726034087913057707479369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6301378783884076943305825 4726034087913057707479369)
            ·
              refine ⟨3544525565934793280609527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4726034087913057707479369 3544525565934793280609527)
              ·
                refine ⟨5316788348902189920914291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544525565934793280609527 5316788348902189920914291)
                ·
                  refine ⟨7975182523353284881371437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5316788348902189920914291 7975182523353284881371437)
                  ·
                    refine ⟨2990693446257481830514289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7975182523353284881371437 2990693446257481830514289)
                    ·
                      refine ⟨2243020084693111372885717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990693446257481830514289 2243020084693111372885717)
                      ·
                        rfl

theorem cell23_4368266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4368266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368266 prefixEnd_4368266 := by exact prefixLift 4368266
  have htrace : WordTrace (prefixWord ++ tailWord_4368266) baseStart_4368266 baseEnd_4368266 := by
    simpa [prefixWord, tailWord_4368266, baseEnd_4368266] using wordTrace_append hprefix tailTrace_4368266
  have hstable : (prefixWord ++ tailWord_4368266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368266).length < 2 ^ (prefixWord ++ tailWord_4368266).sum := by decide
  have hdescent : baseEnd_4368266 < baseStart_4368266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368279 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_4368279 : Nat := 118140960795 + 4368279 * 2 ^ 59
def prefixEnd_4368279 : Nat := 4983230072969 + 3 ^ 40 * 4368279 * 2
def baseEnd_4368279 : Nat := 2243026759941619822023157

theorem tailTrace_4368279 : CollatzResearch.WordTrace tailWord_4368279 prefixEnd_4368279 2243026759941619822023157 := by
  unfold tailWord_4368279
  simp only [CollatzResearch.WordTrace]
  refine ⟨159324224141478700502819891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106216149427652467001879927 159324224141478700502819891)
  ·
    refine ⟨238986336212218050754229837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159324224141478700502819891 238986336212218050754229837)
    ·
      refine ⟨89619876079581769032836189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238986336212218050754229837 89619876079581769032836189)
      ·
        refine ⟨33607453529843163387313571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89619876079581769032836189 33607453529843163387313571)
        ·
          refine ⟨50411180294764745080970357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33607453529843163387313571 50411180294764745080970357)
          ·
            refine ⟨4726048152634194851340971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50411180294764745080970357 4726048152634194851340971)
            ·
              refine ⟨7089072228951292277011457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726048152634194851340971 7089072228951292277011457)
              ·
                refine ⟨5316804171713469207758593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089072228951292277011457 5316804171713469207758593)
                ·
                  refine ⟨3987603128785101905818945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5316804171713469207758593 3987603128785101905818945)
                  ·
                    refine ⟨2990702346588826429364209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3987603128785101905818945 2990702346588826429364209)
                    ·
                      refine ⟨2243026759941619822023157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990702346588826429364209 2243026759941619822023157)
                      ·
                        rfl

theorem cell23_4368279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_4368279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368279 prefixEnd_4368279 := by exact prefixLift 4368279
  have htrace : WordTrace (prefixWord ++ tailWord_4368279) baseStart_4368279 baseEnd_4368279 := by
    simpa [prefixWord, tailWord_4368279, baseEnd_4368279] using wordTrace_append hprefix tailTrace_4368279
  have hstable : (prefixWord ++ tailWord_4368279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368279).length < 2 ^ (prefixWord ++ tailWord_4368279).sum := by decide
  have hdescent : baseEnd_4368279 < baseStart_4368279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368285 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 5]
def baseStart_4368285 : Nat := 118140960795 + 4368285 * 2 ^ 59
def prefixEnd_4368285 : Nat := 4983230072969 + 3 ^ 40 * 4368285 * 2
def baseEnd_4368285 : Nat := 249225537869505199838681

theorem tailTrace_4368285 : CollatzResearch.WordTrace tailWord_4368285 prefixEnd_4368285 249225537869505199838681 := by
  unfold tailWord_4368285
  simp only [CollatzResearch.WordTrace]
  refine ⟨159324442979456963527538309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106216295319637975685025539 159324442979456963527538309)
  ·
    refine ⟨29873333058648180661413433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159324442979456963527538309 29873333058648180661413433)
    ·
      refine ⟨22404999793986135496060075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29873333058648180661413433 22404999793986135496060075)
      ·
        refine ⟨33607499690979203244090113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22404999793986135496060075 33607499690979203244090113)
        ·
          refine ⟨25205624768234402433067585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33607499690979203244090113 25205624768234402433067585)
          ·
            refine ⟨18904218576175801824800689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25205624768234402433067585 18904218576175801824800689)
            ·
              refine ⟨14178163932131851368600517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18904218576175801824800689 14178163932131851368600517)
              ·
                refine ⟨2658405737274722131612597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14178163932131851368600517 2658405737274722131612597)
                ·
                  refine ⟨249225537869505199838681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2658405737274722131612597 249225537869505199838681)
                  ·
                    rfl

theorem cell23_4368285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_4368285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368285 prefixEnd_4368285 := by exact prefixLift 4368285
  have htrace : WordTrace (prefixWord ++ tailWord_4368285) baseStart_4368285 baseEnd_4368285 := by
    simpa [prefixWord, tailWord_4368285, baseEnd_4368285] using wordTrace_append hprefix tailTrace_4368285
  have hstable : (prefixWord ++ tailWord_4368285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368285).length < 2 ^ (prefixWord ++ tailWord_4368285).sum := by decide
  have hdescent : baseEnd_4368285 < baseStart_4368285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368291 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7]
def baseStart_4368291 : Nat := 118140960795 + 4368291 * 2 ^ 59
def prefixEnd_4368291 : Nat := 4983230072969 + 3 ^ 40 * 4368291 * 2
def baseEnd_4368291 : Nat := 2243032921709473775073101

theorem tailTrace_4368291 : CollatzResearch.WordTrace tailWord_4368291 prefixEnd_4368291 2243032921709473775073101 := by
  unfold tailWord_4368291
  simp only [CollatzResearch.WordTrace]
  refine ⟨159324661817435226552256727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106216441211623484368171151 159324661817435226552256727)
  ·
    refine ⟨238986992726152839828385091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159324661817435226552256727 238986992726152839828385091)
    ·
      refine ⟨358480489089229259742577637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238986992726152839828385091 358480489089229259742577637)
      ·
        refine ⟨67215091704230486201733307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 358480489089229259742577637 67215091704230486201733307)
        ·
          refine ⟨100822637556345729302599961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67215091704230486201733307 100822637556345729302599961)
          ·
            refine ⟨75616978167259296976949971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100822637556345729302599961 75616978167259296976949971)
            ·
              refine ⟨113425467250888945465424957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75616978167259296976949971 113425467250888945465424957)
              ·
                refine ⟨42534550219083354549534359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113425467250888945465424957 42534550219083354549534359)
                ·
                  refine ⟨63801825328625031824301539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42534550219083354549534359 63801825328625031824301539)
                  ·
                    refine ⟨95702737992937547736452309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63801825328625031824301539 95702737992937547736452309)
                    ·
                      refine ⟨2243032921709473775073101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95702737992937547736452309 2243032921709473775073101)
                      ·
                        rfl

theorem cell23_4368291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_4368291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368291 prefixEnd_4368291 := by exact prefixLift 4368291
  have htrace : WordTrace (prefixWord ++ tailWord_4368291) baseStart_4368291 baseEnd_4368291 := by
    simpa [prefixWord, tailWord_4368291, baseEnd_4368291] using wordTrace_append hprefix tailTrace_4368291
  have hstable : (prefixWord ++ tailWord_4368291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368291).length < 2 ^ (prefixWord ++ tailWord_4368291).sum := by decide
  have hdescent : baseEnd_4368291 < baseStart_4368291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368295 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4368295 : Nat := 118140960795 + 4368295 * 2 ^ 59
def prefixEnd_4368295 : Nat := 4983230072969 + 3 ^ 40 * 4368295 * 2
def baseEnd_4368295 : Nat := 2243034975632091759423083

theorem tailTrace_4368295 : CollatzResearch.WordTrace tailWord_4368295 prefixEnd_4368295 2243034975632091759423083 := by
  unfold tailWord_4368295
  simp only [CollatzResearch.WordTrace]
  refine ⟨159324807709420735235402339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106216538472947156823601559 159324807709420735235402339)
  ·
    refine ⟨238987211564131102853103509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159324807709420735235402339 238987211564131102853103509)
    ·
      refine ⟨11202525542068645446239227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 238987211564131102853103509 11202525542068645446239227)
      ·
        refine ⟨16803788313102968169358841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11202525542068645446239227 16803788313102968169358841)
        ·
          refine ⟨12602841234827226127019131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16803788313102968169358841 12602841234827226127019131)
          ·
            refine ⟨18904261852240839190528697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602841234827226127019131 18904261852240839190528697)
            ·
              refine ⟨14178196389180629392896523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18904261852240839190528697 14178196389180629392896523)
              ·
                refine ⟨21267294583770944089344785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14178196389180629392896523 21267294583770944089344785)
                ·
                  refine ⟨15950470937828208067008589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21267294583770944089344785 15950470937828208067008589)
                  ·
                    refine ⟨5981426601685578025128221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15950470937828208067008589 5981426601685578025128221)
                    ·
                      refine ⟨2243034975632091759423083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981426601685578025128221 2243034975632091759423083)
                      ·
                        rfl

theorem cell23_4368295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4368295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368295 prefixEnd_4368295 := by exact prefixLift 4368295
  have htrace : WordTrace (prefixWord ++ tailWord_4368295) baseStart_4368295 baseEnd_4368295 := by
    simpa [prefixWord, tailWord_4368295, baseEnd_4368295] using wordTrace_append hprefix tailTrace_4368295
  have hstable : (prefixWord ++ tailWord_4368295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368295).length < 2 ^ (prefixWord ++ tailWord_4368295).sum := by decide
  have hdescent : baseEnd_4368295 < baseStart_4368295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368296 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4368296 : Nat := 118140960795 + 4368296 * 2 ^ 59
def prefixEnd_4368296 : Nat := 4983230072969 + 3 ^ 40 * 4368296 * 2
def baseEnd_4368296 : Nat := 2243035489112746255510579

theorem tailTrace_4368296 : CollatzResearch.WordTrace tailWord_4368296 prefixEnd_4368296 2243035489112746255510579 := by
  unfold tailWord_4368296
  simp only [CollatzResearch.WordTrace]
  refine ⟨79662422091208556203094371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106216562788278074937459161 79662422091208556203094371)
  ·
    refine ⟨119493633136812834304641557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79662422091208556203094371 119493633136812834304641557)
    ·
      refine ⟨5601264053288101608030073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119493633136812834304641557 5601264053288101608030073)
      ·
        refine ⟨4200948039966076206022555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5601264053288101608030073 4200948039966076206022555)
        ·
          refine ⟨6301422059949114309033833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4200948039966076206022555 6301422059949114309033833)
          ·
            refine ⟨4726066544961835731775375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6301422059949114309033833 4726066544961835731775375)
            ·
              refine ⟨7089099817442753597663063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726066544961835731775375 7089099817442753597663063)
              ·
                refine ⟨10633649726164130396494595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7089099817442753597663063 10633649726164130396494595)
                ·
                  refine ⟨15950474589246195594741893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10633649726164130396494595 15950474589246195594741893)
                  ·
                    refine ⟨2990713985483661674014105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15950474589246195594741893 2990713985483661674014105)
                    ·
                      refine ⟨2243035489112746255510579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990713985483661674014105 2243035489112746255510579)
                      ·
                        rfl

theorem cell23_4368296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4368296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368296 prefixEnd_4368296 := by exact prefixLift 4368296
  have htrace : WordTrace (prefixWord ++ tailWord_4368296) baseStart_4368296 baseEnd_4368296 := by
    simpa [prefixWord, tailWord_4368296, baseEnd_4368296] using wordTrace_append hprefix tailTrace_4368296
  have hstable : (prefixWord ++ tailWord_4368296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368296).length < 2 ^ (prefixWord ++ tailWord_4368296).sum := by decide
  have hdescent : baseEnd_4368296 < baseStart_4368296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368311 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 10]
def baseStart_4368311 : Nat := 118140960795 + 4368311 * 2 ^ 59
def prefixEnd_4368311 : Nat := 4983230072969 + 3 ^ 40 * 4368311 * 2
def baseEnd_4368311 : Nat := 747681063774187898941003

theorem tailTrace_4368311 : CollatzResearch.WordTrace tailWord_4368311 prefixEnd_4368311 747681063774187898941003 := by
  unfold tailWord_4368311
  simp only [CollatzResearch.WordTrace]
  refine ⟨159325391277362769967984787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106216927518241846645323191 159325391277362769967984787)
  ·
    refine ⟨238988086916044154951977181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159325391277362769967984787 238988086916044154951977181)
    ·
      refine ⟨89620532593516558106991443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238988086916044154951977181 89620532593516558106991443)
      ·
        refine ⟨134430798890274837160487165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89620532593516558106991443 134430798890274837160487165)
        ·
          refine ⟨50411549583853063935182687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134430798890274837160487165 50411549583853063935182687)
          ·
            refine ⟨75617324375779595902774031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50411549583853063935182687 75617324375779595902774031)
            ·
              refine ⟨113425986563669393854161047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75617324375779595902774031 113425986563669393854161047)
              ·
                refine ⟨170138979845504090781241571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113425986563669393854161047 170138979845504090781241571)
                ·
                  refine ⟨255208469768256136171862357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170138979845504090781241571 255208469768256136171862357)
                  ·
                    refine ⟨747681063774187898941003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 255208469768256136171862357 747681063774187898941003)
                    ·
                      rfl

theorem cell23_4368311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_4368311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368311 prefixEnd_4368311 := by exact prefixLift 4368311
  have htrace : WordTrace (prefixWord ++ tailWord_4368311) baseStart_4368311 baseEnd_4368311 := by
    simpa [prefixWord, tailWord_4368311, baseEnd_4368311] using wordTrace_append hprefix tailTrace_4368311
  have hstable : (prefixWord ++ tailWord_4368311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368311).length < 2 ^ (prefixWord ++ tailWord_4368311).sum := by decide
  have hdescent : baseEnd_4368311 < baseStart_4368311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368342 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4368342 : Nat := 118140960795 + 4368342 * 2 ^ 59
def prefixEnd_4368342 : Nat := 4983230072969 + 3 ^ 40 * 4368342 * 2
def baseEnd_4368342 : Nat := 2243059109222853075535367

theorem tailTrace_4368342 : CollatzResearch.WordTrace tailWord_4368342 prefixEnd_4368342 2243059109222853075535367 := by
  unfold tailWord_4368342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957907621265653891397705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106217681293500308174908853 9957907621265653891397705)
  ·
    refine ⟨7468430715949240418548279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9957907621265653891397705 7468430715949240418548279)
    ·
      refine ⟨11202646073923860627822419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468430715949240418548279 11202646073923860627822419)
      ·
        refine ⟨16803969110885790941733629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11202646073923860627822419 16803969110885790941733629)
        ·
          refine ⟨6301488416582171603150111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16803969110885790941733629 6301488416582171603150111)
          ·
            refine ⟨9452232624873257404725167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301488416582171603150111 9452232624873257404725167)
            ·
              refine ⟨14178348937309886107087751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452232624873257404725167 14178348937309886107087751)
              ·
                refine ⟨21267523405964829160631627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14178348937309886107087751 21267523405964829160631627)
                ·
                  refine ⟨31901285108947243740947441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21267523405964829160631627 31901285108947243740947441)
                  ·
                    refine ⟨23925963831710432805710581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31901285108947243740947441 23925963831710432805710581)
                    ·
                      refine ⟨2243059109222853075535367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23925963831710432805710581 2243059109222853075535367)
                      ·
                        rfl

theorem cell23_4368342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4368342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368342 prefixEnd_4368342 := by exact prefixLift 4368342
  have htrace : WordTrace (prefixWord ++ tailWord_4368342) baseStart_4368342 baseEnd_4368342 := by
    simpa [prefixWord, tailWord_4368342, baseEnd_4368342] using wordTrace_append hprefix tailTrace_4368342
  have hstable : (prefixWord ++ tailWord_4368342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368342).length < 2 ^ (prefixWord ++ tailWord_4368342).sum := by decide
  have hdescent : baseEnd_4368342 < baseStart_4368342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368368 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_4368368 : Nat := 118140960795 + 4368368 * 2 ^ 59
def prefixEnd_4368368 : Nat := 4983230072969 + 3 ^ 40 * 4368368 * 2
def baseEnd_4368368 : Nat := 2243072459719869973810247

theorem tailTrace_4368368 : CollatzResearch.WordTrace tailWord_4368368 prefixEnd_4368368 2243072459719869973810247 := by
  unfold tailWord_4368368
  simp only [CollatzResearch.WordTrace]
  refine ⟨79663735119078134351404879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106218313492104179135206505 79663735119078134351404879)
  ·
    refine ⟨119495602678617201527107319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79663735119078134351404879 119495602678617201527107319)
    ·
      refine ⟨179243404017925802290660979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119495602678617201527107319 179243404017925802290660979)
      ·
        refine ⟨268865106026888703435991469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179243404017925802290660979 268865106026888703435991469)
        ·
          refine ⟨100824414760083263788496801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268865106026888703435991469 100824414760083263788496801)
          ·
            refine ⟨75618311070062447841372601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100824414760083263788496801 75618311070062447841372601)
            ·
              refine ⟨56713733302546835881029451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75618311070062447841372601 56713733302546835881029451)
              ·
                refine ⟨85070599953820253821544177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56713733302546835881029451 85070599953820253821544177)
                ·
                  refine ⟨63802949965365190366158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85070599953820253821544177 63802949965365190366158133)
                  ·
                    refine ⟨5981526559252986596827325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63802949965365190366158133 5981526559252986596827325)
                    ·
                      refine ⟨2243072459719869973810247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981526559252986596827325 2243072459719869973810247)
                      ·
                        rfl

theorem cell23_4368368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_4368368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368368 prefixEnd_4368368 := by exact prefixLift 4368368
  have htrace : WordTrace (prefixWord ++ tailWord_4368368) baseStart_4368368 baseEnd_4368368 := by
    simpa [prefixWord, tailWord_4368368, baseEnd_4368368] using wordTrace_append hprefix tailTrace_4368368
  have hstable : (prefixWord ++ tailWord_4368368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368368).length < 2 ^ (prefixWord ++ tailWord_4368368).sum := by decide
  have hdescent : baseEnd_4368368 < baseStart_4368368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368428 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_4368428 : Nat := 118140960795 + 4368428 * 2 ^ 59
def prefixEnd_4368428 : Nat := 4983230072969 + 3 ^ 40 * 4368428 * 2
def baseEnd_4368428 : Nat := 2243103268559139739059971

theorem tailTrace_4368428 : CollatzResearch.WordTrace tailWord_4368428 prefixEnd_4368428 2243103268559139739059971 := by
  unfold tailWord_4368428
  simp only [CollatzResearch.WordTrace]
  refine ⟨79664829308969449474996969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106219772411959265966662625 79664829308969449474996969)
  ·
    refine ⟨59748621981727087106247727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79664829308969449474996969 59748621981727087106247727)
    ·
      refine ⟨89622932972590630659371591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59748621981727087106247727 89622932972590630659371591)
      ·
        refine ⟨134434399458885945989057387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89622932972590630659371591 134434399458885945989057387)
        ·
          refine ⟨201651599188328918983586081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134434399458885945989057387 201651599188328918983586081)
          ·
            refine ⟨151238699391246689237689561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201651599188328918983586081 151238699391246689237689561)
            ·
              refine ⟨113429024543435016928267171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151238699391246689237689561 113429024543435016928267171)
              ·
                refine ⟨170143536815152525392400757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113429024543435016928267171 170143536815152525392400757)
                ·
                  refine ⟨15950956576420549255537571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170143536815152525392400757 15950956576420549255537571)
                  ·
                    refine ⟨23926434864630823883306357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15950956576420549255537571 23926434864630823883306357)
                    ·
                      refine ⟨2243103268559139739059971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23926434864630823883306357 2243103268559139739059971)
                      ·
                        rfl

theorem cell23_4368428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_4368428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368428 prefixEnd_4368428 := by exact prefixLift 4368428
  have htrace : WordTrace (prefixWord ++ tailWord_4368428) baseStart_4368428 baseEnd_4368428 := by
    simpa [prefixWord, tailWord_4368428, baseEnd_4368428] using wordTrace_append hprefix tailTrace_4368428
  have hstable : (prefixWord ++ tailWord_4368428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368428).length < 2 ^ (prefixWord ++ tailWord_4368428).sum := by decide
  have hdescent : baseEnd_4368428 < baseStart_4368428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368442 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_4368442 : Nat := 118140960795 + 4368442 * 2 ^ 59
def prefixEnd_4368442 : Nat := 4983230072969 + 3 ^ 40 * 4368442 * 2
def baseEnd_4368442 : Nat := 2243110457288302684284907

theorem tailTrace_4368442 : CollatzResearch.WordTrace tailWord_4368442 prefixEnd_4368442 2243110457288302684284907 := by
  unfold tailWord_4368442
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832542309972044835250895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106220112826592119560669053 39832542309972044835250895)
  ·
    refine ⟨59748813464958067252876343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39832542309972044835250895 59748813464958067252876343)
    ·
      refine ⟨89623220197437100879314515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59748813464958067252876343 89623220197437100879314515)
      ·
        refine ⟨134434830296155651318971773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89623220197437100879314515 134434830296155651318971773)
        ·
          refine ⟨50413061361058369244614415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134434830296155651318971773 50413061361058369244614415)
          ·
            refine ⟨75619592041587553866921623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50413061361058369244614415 75619592041587553866921623)
            ·
              refine ⟨113429388062381330800382435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75619592041587553866921623 113429388062381330800382435)
              ·
                refine ⟨170144082093571996200573653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113429388062381330800382435 170144082093571996200573653)
                ·
                  refine ⟨3987751924068093660950945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170144082093571996200573653 3987751924068093660950945)
                  ·
                    refine ⟨2990813943051070245713209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3987751924068093660950945 2990813943051070245713209)
                    ·
                      refine ⟨2243110457288302684284907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2990813943051070245713209 2243110457288302684284907)
                      ·
                        rfl

theorem cell23_4368442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_4368442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368442 prefixEnd_4368442 := by exact prefixLift 4368442
  have htrace : WordTrace (prefixWord ++ tailWord_4368442) baseStart_4368442 baseEnd_4368442 := by
    simpa [prefixWord, tailWord_4368442, baseEnd_4368442] using wordTrace_append hprefix tailTrace_4368442
  have hstable : (prefixWord ++ tailWord_4368442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368442).length < 2 ^ (prefixWord ++ tailWord_4368442).sum := by decide
  have hdescent : baseEnd_4368442 < baseStart_4368442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368445 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4368445 : Nat := 118140960795 + 4368445 * 2 ^ 59
def prefixEnd_4368445 : Nat := 4983230072969 + 3 ^ 40 * 4368445 * 2
def baseEnd_4368445 : Nat := 2243111997730266172547393

theorem tailTrace_4368445 : CollatzResearch.WordTrace tailWord_4368445 prefixEnd_4368445 2243111997730266172547393 := by
  unfold tailWord_4368445
  simp only [CollatzResearch.WordTrace]
  refine ⟨159330278658877310853362789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106220185772584873902241859 159330278658877310853362789)
  ·
    refine ⟨29874427248539495785005523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159330278658877310853362789 29874427248539495785005523)
    ·
      refine ⟨44811640872809243677508285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29874427248539495785005523 44811640872809243677508285)
      ·
        refine ⟨16804365327303466379065607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44811640872809243677508285 16804365327303466379065607)
        ·
          refine ⟨25206547990955199568598411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16804365327303466379065607 25206547990955199568598411)
          ·
            refine ⟨37809821986432799352897617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25206547990955199568598411 37809821986432799352897617)
            ·
              refine ⟨28357366489824599514673213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37809821986432799352897617 28357366489824599514673213)
              ·
                refine ⟨10634012433684224818002455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28357366489824599514673213 10634012433684224818002455)
                ·
                  refine ⟨15951018650526337227003683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10634012433684224818002455 15951018650526337227003683)
                  ·
                    refine ⟨23926527975789505840505525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15951018650526337227003683 23926527975789505840505525)
                    ·
                      refine ⟨2243111997730266172547393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23926527975789505840505525 2243111997730266172547393)
                      ·
                        rfl

theorem cell23_4368445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4368445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368445 prefixEnd_4368445 := by exact prefixLift 4368445
  have htrace : WordTrace (prefixWord ++ tailWord_4368445) baseStart_4368445 baseEnd_4368445 := by
    simpa [prefixWord, tailWord_4368445, baseEnd_4368445] using wordTrace_append hprefix tailTrace_4368445
  have hstable : (prefixWord ++ tailWord_4368445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368445).length < 2 ^ (prefixWord ++ tailWord_4368445).sum := by decide
  have hdescent : baseEnd_4368445 < baseStart_4368445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368448 : List Nat := [2, 1, 1, 2, 2, 5, 10]
def baseStart_4368448 : Nat := 118140960795 + 4368448 * 2 ^ 59
def prefixEnd_4368448 : Nat := 4983230072969 + 3 ^ 40 * 4368448 * 2
def baseEnd_4368448 : Nat := 27692759730521353837159

theorem tailTrace_4368448 : CollatzResearch.WordTrace tailWord_4368448 prefixEnd_4368448 27692759730521353837159 := by
  unfold tailWord_4368448
  simp only [CollatzResearch.WordTrace]
  refine ⟨79665194038933221182860999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106220258718577628243814665 79665194038933221182860999)
  ·
    refine ⟨119497791058399831774291499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79665194038933221182860999 119497791058399831774291499)
    ·
      refine ⟨179246686587599747661437249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119497791058399831774291499 179246686587599747661437249)
      ·
        refine ⟨134435014940699810746077937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179246686587599747661437249 134435014940699810746077937)
        ·
          refine ⟨100826261205524858059558453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134435014940699810746077937 100826261205524858059558453)
          ·
            refine ⟨9452461988017955443083605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100826261205524858059558453 9452461988017955443083605)
            ·
              refine ⟨27692759730521353837159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9452461988017955443083605 27692759730521353837159)
              ·
                rfl

theorem cell23_4368448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 10].length) (baseStart_4368448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368448 prefixEnd_4368448 := by exact prefixLift 4368448
  have htrace : WordTrace (prefixWord ++ tailWord_4368448) baseStart_4368448 baseEnd_4368448 := by
    simpa [prefixWord, tailWord_4368448, baseEnd_4368448] using wordTrace_append hprefix tailTrace_4368448
  have hstable : (prefixWord ++ tailWord_4368448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368448).length < 2 ^ (prefixWord ++ tailWord_4368448).sum := by decide
  have hdescent : baseEnd_4368448 < baseStart_4368448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_4368458 : Nat := 118140960795 + 4368458 * 2 ^ 59
def prefixEnd_4368458 : Nat := 4983230072969 + 3 ^ 40 * 4368458 * 2
def baseEnd_4368458 : Nat := 2243118672978774621684833

theorem tailTrace_4368458 : CollatzResearch.WordTrace tailWord_4368458 prefixEnd_4368458 2243118672978774621684833 := by
  unfold tailWord_4368458
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832688201957553518396507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106220501871886809382390685 39832688201957553518396507)
  ·
    refine ⟨59749032302936330277594761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39832688201957553518396507 59749032302936330277594761)
    ·
      refine ⟨44811774227202247708196071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59749032302936330277594761 44811774227202247708196071)
      ·
        refine ⟨67217661340803371562294107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44811774227202247708196071 67217661340803371562294107)
        ·
          refine ⟨100826492011205057343441161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67217661340803371562294107 100826492011205057343441161)
          ·
            refine ⟨75619869008403793007580871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100826492011205057343441161 75619869008403793007580871)
            ·
              refine ⟨113429803512605689511371307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75619869008403793007580871 113429803512605689511371307)
              ·
                refine ⟨170144705268908534267056961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113429803512605689511371307 170144705268908534267056961)
                ·
                  refine ⟨127608528951681400700292721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170144705268908534267056961 127608528951681400700292721)
                  ·
                    refine ⟨95706396713761050525219541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127608528951681400700292721 95706396713761050525219541)
                    ·
                      refine ⟨2243118672978774621684833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95706396713761050525219541 2243118672978774621684833)
                      ·
                        rfl

theorem cell23_4368458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_4368458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368458 prefixEnd_4368458 := by exact prefixLift 4368458
  have htrace : WordTrace (prefixWord ++ tailWord_4368458) baseStart_4368458 baseEnd_4368458 := by
    simpa [prefixWord, tailWord_4368458, baseEnd_4368458] using wordTrace_append hprefix tailTrace_4368458
  have hstable : (prefixWord ++ tailWord_4368458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368458).length < 2 ^ (prefixWord ++ tailWord_4368458).sum := by decide
  have hdescent : baseEnd_4368458 < baseStart_4368458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368469 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_4368469 : Nat := 118140960795 + 4368469 * 2 ^ 59
def prefixEnd_4368469 : Nat := 4983230072969 + 3 ^ 40 * 4368469 * 2
def baseEnd_4368469 : Nat := 747708107088658026215761

theorem tailTrace_4368469 : CollatzResearch.WordTrace tailWord_4368469 prefixEnd_4368469 747708107088658026215761 := by
  unfold tailWord_4368469
  simp only [CollatzResearch.WordTrace]
  refine ⟨159331154010790362952236461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106220769340526908634824307 159331154010790362952236461)
  ·
    refine ⟨59749182754046386107088673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159331154010790362952236461 59749182754046386107088673)
    ·
      refine ⟨44811887065534789580316505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59749182754046386107088673 44811887065534789580316505)
      ·
        refine ⟨33608915299151092185237379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44811887065534789580316505 33608915299151092185237379)
        ·
          refine ⟨50413372948726638277856069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33608915299151092185237379 50413372948726638277856069)
          ·
            refine ⟨9452507427886244677098013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50413372948726638277856069 9452507427886244677098013)
            ·
              refine ⟨3544690285457341753911755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9452507427886244677098013 3544690285457341753911755)
              ·
                refine ⟨5317035428186012630867633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544690285457341753911755 5317035428186012630867633)
                ·
                  refine ⟨3987776571139509473150725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5317035428186012630867633 3987776571139509473150725)
                  ·
                    refine ⟨747708107088658026215761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3987776571139509473150725 747708107088658026215761)
                    ·
                      rfl

theorem cell23_4368469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_4368469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368469 prefixEnd_4368469 := by exact prefixLift 4368469
  have htrace : WordTrace (prefixWord ++ tailWord_4368469) baseStart_4368469 baseEnd_4368469 := by
    simpa [prefixWord, tailWord_4368469, baseEnd_4368469] using wordTrace_append hprefix tailTrace_4368469
  have hstable : (prefixWord ++ tailWord_4368469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368469).length < 2 ^ (prefixWord ++ tailWord_4368469).sum := by decide
  have hdescent : baseEnd_4368469 < baseStart_4368469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368472 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_4368472 : Nat := 118140960795 + 4368472 * 2 ^ 59
def prefixEnd_4368472 : Nat := 4983230072969 + 3 ^ 40 * 4368472 * 2
def baseEnd_4368472 : Nat := 2243125861707937566909769

theorem tailTrace_4368472 : CollatzResearch.WordTrace tailWord_4368472 prefixEnd_4368472 2243125861707937566909769 := by
  unfold tailWord_4368472
  simp only [CollatzResearch.WordTrace]
  refine ⟨79665631714889747232297835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106220842286519662976397113 79665631714889747232297835)
  ·
    refine ⟨119498447572334620848446753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79665631714889747232297835 119498447572334620848446753)
    ·
      refine ⟨89623835679250965636335065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119498447572334620848446753 89623835679250965636335065)
      ·
        refine ⟨67217876759438224227251299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89623835679250965636335065 67217876759438224227251299)
        ·
          refine ⟨100826815139157336340876949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67217876759438224227251299 100826815139157336340876949)
          ·
            refine ⟨4726256959648000140978607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100826815139157336340876949 4726256959648000140978607)
            ·
              refine ⟨7089385439472000211467911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726256959648000140978607 7089385439472000211467911)
              ·
                refine ⟨10634078159208000317201867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7089385439472000211467911 10634078159208000317201867)
                ·
                  refine ⟨15951117238812000475802801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10634078159208000317201867 15951117238812000475802801)
                  ·
                    refine ⟨11963337929109000356852101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15951117238812000475802801 11963337929109000356852101)
                    ·
                      refine ⟨2243125861707937566909769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11963337929109000356852101 2243125861707937566909769)
                      ·
                        rfl

theorem cell23_4368472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_4368472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368472 prefixEnd_4368472 := by exact prefixLift 4368472
  have htrace : WordTrace (prefixWord ++ tailWord_4368472) baseStart_4368472 baseEnd_4368472 := by
    simpa [prefixWord, tailWord_4368472, baseEnd_4368472] using wordTrace_append hprefix tailTrace_4368472
  have hstable : (prefixWord ++ tailWord_4368472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368472).length < 2 ^ (prefixWord ++ tailWord_4368472).sum := by decide
  have hdescent : baseEnd_4368472 < baseStart_4368472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368482 : List Nat := [3, 3, 2, 2, 2, 1, 1, 9]
def baseStart_4368482 : Nat := 118140960795 + 4368482 * 2 ^ 59
def prefixEnd_4368482 : Nat := 4983230072969 + 3 ^ 40 * 4368482 * 2
def baseEnd_4368482 : Nat := 83078925796832686214249

theorem tailTrace_4368482 : CollatzResearch.WordTrace tailWord_4368482 prefixEnd_4368482 83078925796832686214249 := by
  unfold tailWord_4368482
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832907039935816543114925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106221085439828844114973133 39832907039935816543114925)
  ·
    refine ⟨14937340139975931203668097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39832907039935816543114925 14937340139975931203668097)
    ·
      refine ⟨11203005104981948402751073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14937340139975931203668097 11203005104981948402751073)
      ·
        refine ⟨8402253828736461302063305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11203005104981948402751073 8402253828736461302063305)
        ·
          refine ⟨6301690371552345976547479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8402253828736461302063305 6301690371552345976547479)
          ·
            refine ⟨9452535557328518964821219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301690371552345976547479 9452535557328518964821219)
            ·
              refine ⟨14178803335992778447231829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452535557328518964821219 14178803335992778447231829)
              ·
                refine ⟨83078925796832686214249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14178803335992778447231829 83078925796832686214249)
                ·
                  rfl

theorem cell23_4368482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_4368482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368482 prefixEnd_4368482 := by exact prefixLift 4368482
  have htrace : WordTrace (prefixWord ++ tailWord_4368482) baseStart_4368482 baseEnd_4368482 := by
    simpa [prefixWord, tailWord_4368482, baseEnd_4368482] using wordTrace_append hprefix tailTrace_4368482
  have hstable : (prefixWord ++ tailWord_4368482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368482).length < 2 ^ (prefixWord ++ tailWord_4368482).sum := by decide
  have hdescent : baseEnd_4368482 < baseStart_4368482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368492 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_4368492 : Nat := 118140960795 + 4368492 * 2 ^ 59
def prefixEnd_4368492 : Nat := 4983230072969 + 3 ^ 40 * 4368492 * 2
def baseEnd_4368492 : Nat := 2243136131321027488659677

theorem tailTrace_4368492 : CollatzResearch.WordTrace tailWord_4368492 prefixEnd_4368492 2243136131321027488659677 := by
  unfold tailWord_4368492
  simp only [CollatzResearch.WordTrace]
  refine ⟨79665996444853518940161865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106221328593138025253549153 79665996444853518940161865)
  ·
    refine ⟨59749497333640139205121399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79665996444853518940161865 59749497333640139205121399)
    ·
      refine ⟨89624246000460208807682099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59749497333640139205121399 89624246000460208807682099)
      ·
        refine ⟨134436369000690313211523149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89624246000460208807682099 134436369000690313211523149)
        ·
          refine ⟨50413638375258867454321181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134436369000690313211523149 50413638375258867454321181)
          ·
            refine ⟨18905114390722075295370443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50413638375258867454321181 18905114390722075295370443)
            ·
              refine ⟨28357671586083112943055665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18905114390722075295370443 28357671586083112943055665)
              ·
                refine ⟨21268253689562334707291749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28357671586083112943055665 21268253689562334707291749)
                ·
                  refine ⟨3987797566792937757617203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21268253689562334707291749 3987797566792937757617203)
                  ·
                    refine ⟨5981696350189406636425805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3987797566792937757617203 5981696350189406636425805)
                    ·
                      refine ⟨2243136131321027488659677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981696350189406636425805 2243136131321027488659677)
                      ·
                        rfl

theorem cell23_4368492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_4368492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368492 prefixEnd_4368492 := by exact prefixLift 4368492
  have htrace : WordTrace (prefixWord ++ tailWord_4368492) baseStart_4368492 baseEnd_4368492 := by
    simpa [prefixWord, tailWord_4368492, baseEnd_4368492] using wordTrace_append hprefix tailTrace_4368492
  have hstable : (prefixWord ++ tailWord_4368492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368492).length < 2 ^ (prefixWord ++ tailWord_4368492).sum := by decide
  have hdescent : baseEnd_4368492 < baseStart_4368492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368526 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4368526 : Nat := 118140960795 + 4368526 * 2 ^ 59
def prefixEnd_4368526 : Nat := 4983230072969 + 3 ^ 40 * 4368526 * 2
def baseEnd_4368526 : Nat := 2243153589663280355634521

theorem tailTrace_4368526 : CollatzResearch.WordTrace tailWord_4368526 prefixEnd_4368526 2243153589663280355634521 := by
  unfold tailWord_4368526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19916654121447982710882679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106222155314389241124707621 19916654121447982710882679)
  ·
    refine ⟨29874981182171974066324019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19916654121447982710882679 29874981182171974066324019)
    ·
      refine ⟨44812471773257961099486029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29874981182171974066324019 44812471773257961099486029)
      ·
        refine ⟨16804676914971735412307261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44812471773257961099486029 16804676914971735412307261)
        ·
          refine ⟨6301753843114400779615223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16804676914971735412307261 6301753843114400779615223)
          ·
            refine ⟨9452630764671601169422835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301753843114400779615223 9452630764671601169422835)
            ·
              refine ⟨14178946147007401754134253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452630764671601169422835 14178946147007401754134253)
              ·
                refine ⟨5317104805127775657800345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14178946147007401754134253 5317104805127775657800345)
                ·
                  refine ⟨3987828603845831743350259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5317104805127775657800345 3987828603845831743350259)
                  ·
                    refine ⟨5981742905768747615025389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3987828603845831743350259 5981742905768747615025389)
                    ·
                      refine ⟨2243153589663280355634521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5981742905768747615025389 2243153589663280355634521)
                      ·
                        rfl

theorem cell23_4368526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4368526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368526 prefixEnd_4368526 := by exact prefixLift 4368526
  have htrace : WordTrace (prefixWord ++ tailWord_4368526) baseStart_4368526 baseEnd_4368526 := by
    simpa [prefixWord, tailWord_4368526, baseEnd_4368526] using wordTrace_append hprefix tailTrace_4368526
  have hstable : (prefixWord ++ tailWord_4368526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368526).length < 2 ^ (prefixWord ++ tailWord_4368526).sum := by decide
  have hdescent : baseEnd_4368526 < baseStart_4368526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368602 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_4368602 : Nat := 118140960795 + 4368602 * 2 ^ 59
def prefixEnd_4368602 : Nat := 4983230072969 + 3 ^ 40 * 4368602 * 2
def baseEnd_4368602 : Nat := 747730871397674019428057

theorem tailTrace_4368602 : CollatzResearch.WordTrace tailWord_4368602 prefixEnd_4368602 747730871397674019428057 := by
  unfold tailWord_4368602
  simp only [CollatzResearch.WordTrace]
  refine ⟨39834001229827131666707015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106224003279539017777885373 39834001229827131666707015)
  ·
    refine ⟨59751001844740697500060523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39834001229827131666707015 59751001844740697500060523)
    ·
      refine ⟨89626502767111046250090785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59751001844740697500060523 89626502767111046250090785)
      ·
        refine ⟨67219877075333284687568089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89626502767111046250090785 67219877075333284687568089)
        ·
          refine ⟨50414907806499963515676067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67219877075333284687568089 50414907806499963515676067)
          ·
            refine ⟨75622361709749945273514101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50414907806499963515676067 75622361709749945273514101)
            ·
              refine ⟨7089596410289057369391947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75622361709749945273514101 7089596410289057369391947)
              ·
                refine ⟨10634394615433586054087921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7089596410289057369391947 10634394615433586054087921)
                ·
                  refine ⟨7975795961575189540565941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10634394615433586054087921 7975795961575189540565941)
                  ·
                    refine ⟨747730871397674019428057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7975795961575189540565941 747730871397674019428057)
                    ·
                      rfl

theorem cell23_4368602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_4368602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368602 prefixEnd_4368602 := by exact prefixLift 4368602
  have htrace : WordTrace (prefixWord ++ tailWord_4368602) baseStart_4368602 baseEnd_4368602 := by
    simpa [prefixWord, tailWord_4368602, baseEnd_4368602] using wordTrace_append hprefix tailTrace_4368602
  have hstable : (prefixWord ++ tailWord_4368602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368602).length < 2 ^ (prefixWord ++ tailWord_4368602).sum := by decide
  have hdescent : baseEnd_4368602 < baseStart_4368602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368622 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4368622 : Nat := 118140960795 + 4368622 * 2 ^ 59
def prefixEnd_4368622 : Nat := 4983230072969 + 3 ^ 40 * 4368622 * 2
def baseEnd_4368622 : Nat := 2243202883806111980034079

theorem tailTrace_4368622 : CollatzResearch.WordTrace tailWord_4368622 prefixEnd_4368622 2243202883806111980034079 := by
  unfold tailWord_4368622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917091797404508760319515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106224489586157380055037413 19917091797404508760319515)
  ·
    refine ⟨29875637696106763140479273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19917091797404508760319515 29875637696106763140479273)
    ·
      refine ⟨22406728272080072355359455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29875637696106763140479273 22406728272080072355359455)
      ·
        refine ⟨33610092408120108533039183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22406728272080072355359455 33610092408120108533039183)
        ·
          refine ⟨50415138612180162799558775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33610092408120108533039183 50415138612180162799558775)
          ·
            refine ⟨75622707918270244199338163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50415138612180162799558775 75622707918270244199338163)
            ·
              refine ⟨113434061877405366299007245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75622707918270244199338163 113434061877405366299007245)
              ·
                refine ⟨42537773204027012362127717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113434061877405366299007245 42537773204027012362127717)
                ·
                  refine ⟨7975832475755064817898947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42537773204027012362127717 7975832475755064817898947)
                  ·
                    refine ⟨11963748713632597226848421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7975832475755064817898947 11963748713632597226848421)
                    ·
                      refine ⟨2243202883806111980034079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11963748713632597226848421 2243202883806111980034079)
                      ·
                        rfl

theorem cell23_4368622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4368622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368622 prefixEnd_4368622 := by exact prefixLift 4368622
  have htrace : WordTrace (prefixWord ++ tailWord_4368622) baseStart_4368622 baseEnd_4368622 := by
    simpa [prefixWord, tailWord_4368622, baseEnd_4368622] using wordTrace_append hprefix tailTrace_4368622
  have hstable : (prefixWord ++ tailWord_4368622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368622).length < 2 ^ (prefixWord ++ tailWord_4368622).sum := by decide
  have hdescent : baseEnd_4368622 < baseStart_4368622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368625 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_4368625 : Nat := 118140960795 + 4368625 * 2 ^ 59
def prefixEnd_4368625 : Nat := 4983230072969 + 3 ^ 40 * 4368625 * 2
def baseEnd_4368625 : Nat := 2243204424248075468296565

theorem tailTrace_4368625 : CollatzResearch.WordTrace tailWord_4368625 prefixEnd_4368625 2243204424248075468296565 := by
  unfold tailWord_4368625
  simp only [CollatzResearch.WordTrace]
  refine ⟨159336843798225201594915329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106224562532150134396610219 159336843798225201594915329)
  ·
    refine ⟨119502632848668901196186497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159336843798225201594915329 119502632848668901196186497)
    ·
      refine ⟨89626974636501675897139873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119502632848668901196186497 89626974636501675897139873)
      ·
        refine ⟨67220230977376256922854905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89626974636501675897139873 67220230977376256922854905)
        ·
          refine ⟨50415173233032192692141179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67220230977376256922854905 50415173233032192692141179)
          ·
            refine ⟨75622759849548289038211769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50415173233032192692141179 75622759849548289038211769)
            ·
              refine ⟨56717069887161216778658827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75622759849548289038211769 56717069887161216778658827)
              ·
                refine ⟨85075604830741825167988241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56717069887161216778658827 85075604830741825167988241)
                ·
                  refine ⟨63806703623056368875991181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85075604830741825167988241 63806703623056368875991181)
                  ·
                    refine ⟨23927513858646138328496693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63806703623056368875991181 23927513858646138328496693)
                    ·
                      refine ⟨2243204424248075468296565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23927513858646138328496693 2243204424248075468296565)
                      ·
                        rfl

theorem cell23_4368625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_4368625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368625 prefixEnd_4368625 := by exact prefixLift 4368625
  have htrace : WordTrace (prefixWord ++ tailWord_4368625) baseStart_4368625 baseEnd_4368625 := by
    simpa [prefixWord, tailWord_4368625, baseEnd_4368625] using wordTrace_append hprefix tailTrace_4368625
  have hstable : (prefixWord ++ tailWord_4368625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368625).length < 2 ^ (prefixWord ++ tailWord_4368625).sum := by decide
  have hdescent : baseEnd_4368625 < baseStart_4368625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368716 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4368716 : Nat := 118140960795 + 4368716 * 2 ^ 59
def prefixEnd_4368716 : Nat := 4983230072969 + 3 ^ 40 * 4368716 * 2
def baseEnd_4368716 : Nat := 2243251150987634612258647

theorem tailTrace_4368716 : CollatzResearch.WordTrace tailWord_4368716 prefixEnd_4368716 2243251150987634612258647 := by
  unfold tailWord_4368716
  simp only [CollatzResearch.WordTrace]
  refine ⟨79670081420447762068239001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106226775227263682757652001 79670081420447762068239001)
  ·
    refine ⟨59752561065335821551179251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79670081420447762068239001 59752561065335821551179251)
    ·
      refine ⟨89628841598003732326768877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59752561065335821551179251 89628841598003732326768877)
      ·
        refine ⟨33610815599251399622538329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89628841598003732326768877 33610815599251399622538329)
        ·
          refine ⟨25208111699438549716903747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33610815599251399622538329 25208111699438549716903747)
          ·
            refine ⟨37812167549157824575355621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25208111699438549716903747 37812167549157824575355621)
            ·
              refine ⟨7089781415467092107879179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37812167549157824575355621 7089781415467092107879179)
              ·
                refine ⟨10634672123200638161818769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7089781415467092107879179 10634672123200638161818769)
                ·
                  refine ⟨7976004092400478621364077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10634672123200638161818769 7976004092400478621364077)
                  ·
                    refine ⟨2991001534650179483011529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7976004092400478621364077 2991001534650179483011529)
                    ·
                      refine ⟨2243251150987634612258647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991001534650179483011529 2243251150987634612258647)
                      ·
                        rfl

theorem cell23_4368716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4368716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368716 prefixEnd_4368716 := by exact prefixLift 4368716
  have htrace : WordTrace (prefixWord ++ tailWord_4368716) baseStart_4368716 baseEnd_4368716 := by
    simpa [prefixWord, tailWord_4368716, baseEnd_4368716] using wordTrace_append hprefix tailTrace_4368716
  have hstable : (prefixWord ++ tailWord_4368716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368716).length < 2 ^ (prefixWord ++ tailWord_4368716).sum := by decide
  have hdescent : baseEnd_4368716 < baseStart_4368716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368722 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_4368722 : Nat := 118140960795 + 4368722 * 2 ^ 59
def prefixEnd_4368722 : Nat := 4983230072969 + 3 ^ 40 * 4368722 * 2
def baseEnd_4368722 : Nat := 747751410623853862927873

theorem tailTrace_4368722 : CollatzResearch.WordTrace tailWord_4368722 prefixEnd_4368722 747751410623853862927873 := by
  unfold tailWord_4368722
  simp only [CollatzResearch.WordTrace]
  refine ⟨39835095419718446790299105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106226921119249191440797613 39835095419718446790299105)
  ·
    refine ⟨29876321564788835092724329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39835095419718446790299105 29876321564788835092724329)
    ·
      refine ⟨22407241173591626319543247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29876321564788835092724329 22407241173591626319543247)
      ·
        refine ⟨33610861760387439479314871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22407241173591626319543247 33610861760387439479314871)
        ·
          refine ⟨50416292640581159218972307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33610861760387439479314871 50416292640581159218972307)
          ·
            refine ⟨75624438960871738828458461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50416292640581159218972307 75624438960871738828458461)
            ·
              refine ⟨28359164610326902060671923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75624438960871738828458461 28359164610326902060671923)
              ·
                refine ⟨42538746915490353091007885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28359164610326902060671923 42538746915490353091007885)
                ·
                  refine ⟨15952030093308882409127957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42538746915490353091007885 15952030093308882409127957)
                  ·
                    refine ⟨747751410623853862927873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15952030093308882409127957 747751410623853862927873)
                    ·
                      rfl

theorem cell23_4368722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_4368722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368722 prefixEnd_4368722 := by exact prefixLift 4368722
  have htrace : WordTrace (prefixWord ++ tailWord_4368722) baseStart_4368722 baseEnd_4368722 := by
    simpa [prefixWord, tailWord_4368722, baseEnd_4368722] using wordTrace_append hprefix tailTrace_4368722
  have hstable : (prefixWord ++ tailWord_4368722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368722).length < 2 ^ (prefixWord ++ tailWord_4368722).sum := by decide
  have hdescent : baseEnd_4368722 < baseStart_4368722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368734 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4368734 : Nat := 118140960795 + 4368734 * 2 ^ 59
def prefixEnd_4368734 : Nat := 4983230072969 + 3 ^ 40 * 4368734 * 2
def baseEnd_4368734 : Nat := 747753464546471847277855

theorem tailTrace_4368734 : CollatzResearch.WordTrace tailWord_4368734 prefixEnd_4368734 747753464546471847277855 := by
  unfold tailWord_4368734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917602419353789151329157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106227212903220208807088837 19917602419353789151329157)
  ·
    refine ⟨3734550453628835465874217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19917602419353789151329157 3734550453628835465874217)
    ·
      refine ⟨2800912840221626599405663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3734550453628835465874217 2800912840221626599405663)
      ·
        refine ⟨4201369260332439899108495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800912840221626599405663 4201369260332439899108495)
        ·
          refine ⟨6302053890498659848662743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201369260332439899108495 6302053890498659848662743)
          ·
            refine ⟨9453080835747989772994115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302053890498659848662743 9453080835747989772994115)
            ·
              refine ⟨14179621253621984659491173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453080835747989772994115 14179621253621984659491173)
              ·
                refine ⟨2658678985054122123654595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14179621253621984659491173 2658678985054122123654595)
                ·
                  refine ⟨3988018477581183185481893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2658678985054122123654595 3988018477581183185481893)
                  ·
                    refine ⟨747753464546471847277855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3988018477581183185481893 747753464546471847277855)
                    ·
                      rfl

theorem cell23_4368734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4368734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368734 prefixEnd_4368734 := by exact prefixLift 4368734
  have htrace : WordTrace (prefixWord ++ tailWord_4368734) baseStart_4368734 baseEnd_4368734 := by
    simpa [prefixWord, tailWord_4368734, baseEnd_4368734] using wordTrace_append hprefix tailTrace_4368734
  have hstable : (prefixWord ++ tailWord_4368734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368734).length < 2 ^ (prefixWord ++ tailWord_4368734).sum := by decide
  have hdescent : baseEnd_4368734 < baseStart_4368734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368749 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4368749 : Nat := 118140960795 + 4368749 * 2 ^ 59
def prefixEnd_4368749 : Nat := 4983230072969 + 3 ^ 40 * 4368749 * 2
def baseEnd_4368749 : Nat := 2243268095849232983145995

theorem tailTrace_4368749 : CollatzResearch.WordTrace tailWord_4368749 prefixEnd_4368749 2243268095849232983145995 := by
  unfold tailWord_4368749
  simp only [CollatzResearch.WordTrace]
  refine ⟨159341366449775970772429301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106227577633183980514952867 159341366449775970772429301)
  ·
    refine ⟨14938253104666497259915247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159341366449775970772429301 14938253104666497259915247)
    ·
      refine ⟨22407379656999745889872871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14938253104666497259915247 22407379656999745889872871)
      ·
        refine ⟨33611069485499618834809307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22407379656999745889872871 33611069485499618834809307)
        ·
          refine ⟨50416604228249428252213961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33611069485499618834809307 50416604228249428252213961)
          ·
            refine ⟨37812453171187071189160471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50416604228249428252213961 37812453171187071189160471)
            ·
              refine ⟨56718679756780606783740707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37812453171187071189160471 56718679756780606783740707)
              ·
                refine ⟨85078019635170910175611061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56718679756780606783740707 85078019635170910175611061)
                ·
                  refine ⟨7976064340797272828963537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85078019635170910175611061 7976064340797272828963537)
                  ·
                    refine ⟨5982048255597954621722653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7976064340797272828963537 5982048255597954621722653)
                    ·
                      refine ⟨2243268095849232983145995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5982048255597954621722653 2243268095849232983145995)
                      ·
                        rfl

theorem cell23_4368749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4368749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368749 prefixEnd_4368749 := by exact prefixLift 4368749
  have htrace : WordTrace (prefixWord ++ tailWord_4368749) baseStart_4368749 baseEnd_4368749 := by
    simpa [prefixWord, tailWord_4368749, baseEnd_4368749] using wordTrace_append hprefix tailTrace_4368749
  have hstable : (prefixWord ++ tailWord_4368749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368749).length < 2 ^ (prefixWord ++ tailWord_4368749).sum := by decide
  have hdescent : baseEnd_4368749 < baseStart_4368749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368752 : List Nat := [2, 1, 1, 1, 4, 3, 3, 8]
def baseStart_4368752 : Nat := 118140960795 + 4368752 * 2 ^ 59
def prefixEnd_4368752 : Nat := 4983230072969 + 3 ^ 40 * 4368752 * 2
def baseEnd_4368752 : Nat := 83084060603377647089203

theorem tailTrace_4368752 : CollatzResearch.WordTrace tailWord_4368752 prefixEnd_4368752 83084060603377647089203 := by
  unfold tailWord_4368752
  simp only [CollatzResearch.WordTrace]
  refine ⟨79670737934382551142394255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106227650579176734856525673 79670737934382551142394255)
  ·
    refine ⟨119506106901573826713591383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79670737934382551142394255 119506106901573826713591383)
    ·
      refine ⟨179259160352360740070387075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119506106901573826713591383 179259160352360740070387075)
      ·
        refine ⟨268888740528541110105580613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179259160352360740070387075 268888740528541110105580613)
        ·
          refine ⟨50416638849101458144796365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268888740528541110105580613 50416638849101458144796365)
          ·
            refine ⟨18906239568413046804298637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50416638849101458144796365 18906239568413046804298637)
            ·
              refine ⟨7089839838154892551611989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18906239568413046804298637 7089839838154892551611989)
              ·
                refine ⟨83084060603377647089203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7089839838154892551611989 83084060603377647089203)
                ·
                  rfl

theorem cell23_4368752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 8].length) (baseStart_4368752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368752 prefixEnd_4368752 := by exact prefixLift 4368752
  have htrace : WordTrace (prefixWord ++ tailWord_4368752) baseStart_4368752 baseEnd_4368752 := by
    simpa [prefixWord, tailWord_4368752, baseEnd_4368752] using wordTrace_append hprefix tailTrace_4368752
  have hstable : (prefixWord ++ tailWord_4368752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368752).length < 2 ^ (prefixWord ++ tailWord_4368752).sum := by decide
  have hdescent : baseEnd_4368752 < baseStart_4368752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368779 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3]
def baseStart_4368779 : Nat := 118140960795 + 4368779 * 2 ^ 59
def prefixEnd_4368779 : Nat := 4983230072969 + 3 ^ 40 * 4368779 * 2
def baseEnd_4368779 : Nat := 2243283500268867865770857

theorem tailTrace_4368779 : CollatzResearch.WordTrace tailWord_4368779 prefixEnd_4368779 2243283500268867865770857 := by
  unfold tailWord_4368779
  simp only [CollatzResearch.WordTrace]
  refine ⟨159342460639667285896021391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106228307093111523930680927 159342460639667285896021391)
  ·
    refine ⟨239013690959500928844032087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159342460639667285896021391 239013690959500928844032087)
    ·
      refine ⟨358520536439251393266048131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239013690959500928844032087 358520536439251393266048131)
      ·
        refine ⟨537780804658877089899072197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358520536439251393266048131 537780804658877089899072197)
        ·
          refine ⟨100833900873539454356076037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 537780804658877089899072197 100833900873539454356076037)
          ·
            refine ⟨18906356413788647691764257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100833900873539454356076037 18906356413788647691764257)
            ·
              refine ⟨14179767310341485768823193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18906356413788647691764257 14179767310341485768823193)
              ·
                refine ⟨10634825482756114326617395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14179767310341485768823193 10634825482756114326617395)
                ·
                  refine ⟨15952238224134171489926093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10634825482756114326617395 15952238224134171489926093)
                  ·
                    refine ⟨5982089334050314308722285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15952238224134171489926093 5982089334050314308722285)
                    ·
                      refine ⟨2243283500268867865770857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5982089334050314308722285 2243283500268867865770857)
                      ·
                        rfl

theorem cell23_4368779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 3].length) (baseStart_4368779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368779 prefixEnd_4368779 := by exact prefixLift 4368779
  have htrace : WordTrace (prefixWord ++ tailWord_4368779) baseStart_4368779 baseEnd_4368779 := by
    simpa [prefixWord, tailWord_4368779, baseEnd_4368779] using wordTrace_append hprefix tailTrace_4368779
  have hstable : (prefixWord ++ tailWord_4368779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368779).length < 2 ^ (prefixWord ++ tailWord_4368779).sum := by decide
  have hdescent : baseEnd_4368779 < baseStart_4368779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368780 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 1, 2, 2]
def baseStart_4368780 : Nat := 118140960795 + 4368780 * 2 ^ 59
def prefixEnd_4368780 : Nat := 4983230072969 + 3 ^ 40 * 4368780 * 2
def baseEnd_4368780 : Nat := 2243284013749522361858353

theorem tailTrace_4368780 : CollatzResearch.WordTrace tailWord_4368780 prefixEnd_4368780 2243284013749522361858353 := by
  unfold tailWord_4368780
  simp only [CollatzResearch.WordTrace]
  refine ⟨79671248556331831533403897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106228331408442442044538529 79671248556331831533403897)
  ·
    refine ⟨59753436417248873650052923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79671248556331831533403897 59753436417248873650052923)
    ·
      refine ⟨89630154625873310475079385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59753436417248873650052923 89630154625873310475079385)
      ·
        refine ⟨67222615969404982856309539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89630154625873310475079385 67222615969404982856309539)
        ·
          refine ⟨100833923954107474284464309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67222615969404982856309539 100833923954107474284464309)
          ·
            refine ⟨9453180370697575714168529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100833923954107474284464309 9453180370697575714168529)
            ·
              refine ⟨7089885278023181785626397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9453180370697575714168529 7089885278023181785626397)
              ·
                refine ⟨2658706979258693169609899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7089885278023181785626397 2658706979258693169609899)
                ·
                  refine ⟨3988060468888039754414849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2658706979258693169609899 3988060468888039754414849)
                  ·
                    refine ⟨2991045351666029815811137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3988060468888039754414849 2991045351666029815811137)
                    ·
                      refine ⟨2243284013749522361858353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991045351666029815811137 2243284013749522361858353)
                      ·
                        rfl

theorem cell23_4368780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_4368780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368780 prefixEnd_4368780 := by exact prefixLift 4368780
  have htrace : WordTrace (prefixWord ++ tailWord_4368780) baseStart_4368780 baseEnd_4368780 := by
    simpa [prefixWord, tailWord_4368780, baseEnd_4368780] using wordTrace_append hprefix tailTrace_4368780
  have hstable : (prefixWord ++ tailWord_4368780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368780).length < 2 ^ (prefixWord ++ tailWord_4368780).sum := by decide
  have hdescent : baseEnd_4368780 < baseStart_4368780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368820 : List Nat := [2, 5, 2, 2, 1, 2, 2, 7]
def baseStart_4368820 : Nat := 118140960795 + 4368820 * 2 ^ 59
def prefixEnd_4368820 : Nat := 4983230072969 + 3 ^ 40 * 4368820 * 2
def baseEnd_4368820 : Nat := 83085353813914896494747

theorem tailTrace_4368820 : CollatzResearch.WordTrace tailWord_4368820 prefixEnd_4368820 83085353813914896494747 := by
  unfold tailWord_4368820
  simp only [CollatzResearch.WordTrace]
  refine ⟨79671978016259374949131957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106229304021679166598842609 79671978016259374949131957)
  ·
    refine ⟨7469247939024316401481121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79671978016259374949131957 7469247939024316401481121)
    ·
      refine ⟨5601935954268237301110841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7469247939024316401481121 5601935954268237301110841)
      ·
        refine ⟨4201451965701177975833131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5601935954268237301110841 4201451965701177975833131)
        ·
          refine ⟨6302177948551766963749697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201451965701177975833131 6302177948551766963749697)
          ·
            refine ⟨4726633461413825222812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6302177948551766963749697 4726633461413825222812273)
            ·
              refine ⟨3544975096060368917109205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4726633461413825222812273 3544975096060368917109205)
              ·
                refine ⟨83085353813914896494747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3544975096060368917109205 83085353813914896494747)
                ·
                  rfl

theorem cell23_4368820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 7].length) (baseStart_4368820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368820 prefixEnd_4368820 := by exact prefixLift 4368820
  have htrace : WordTrace (prefixWord ++ tailWord_4368820) baseStart_4368820 baseEnd_4368820 := by
    simpa [prefixWord, tailWord_4368820, baseEnd_4368820] using wordTrace_append hprefix tailTrace_4368820
  have hstable : (prefixWord ++ tailWord_4368820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368820).length < 2 ^ (prefixWord ++ tailWord_4368820).sum := by decide
  have hdescent : baseEnd_4368820 < baseStart_4368820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368823 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_4368823 : Nat := 118140960795 + 4368823 * 2 ^ 59
def prefixEnd_4368823 : Nat := 4983230072969 + 3 ^ 40 * 4368823 * 2
def baseEnd_4368823 : Nat := 2243306093417665693620655

theorem tailTrace_4368823 : CollatzResearch.WordTrace tailWord_4368823 prefixEnd_4368823 2243306093417665693620655 := by
  unfold tailWord_4368823
  simp only [CollatzResearch.WordTrace]
  refine ⟨159344065451507881410623123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106229376967671920940415415 159344065451507881410623123)
  ·
    refine ⟨239016098177261822115934685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159344065451507881410623123 239016098177261822115934685)
    ·
      refine ⟨89631036816473183293475507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239016098177261822115934685 89631036816473183293475507)
      ·
        refine ⟨134446555224709774940213261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89631036816473183293475507 134446555224709774940213261)
        ·
          refine ⟨50417458209266165602579973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134446555224709774940213261 50417458209266165602579973)
          ·
            refine ⟨9453273414237406050483745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50417458209266165602579973 9453273414237406050483745)
            ·
              refine ⟨7089955060678054537862809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9453273414237406050483745 7089955060678054537862809)
              ·
                refine ⟨5317466295508540903397107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089955060678054537862809 5317466295508540903397107)
                ·
                  refine ⟨7976199443262811355095661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5317466295508540903397107 7976199443262811355095661)
                  ·
                    refine ⟨2991074791223554258160873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7976199443262811355095661 2991074791223554258160873)
                    ·
                      refine ⟨2243306093417665693620655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991074791223554258160873 2243306093417665693620655)
                      ·
                        rfl

theorem cell23_4368823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_4368823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368823 prefixEnd_4368823 := by exact prefixLift 4368823
  have htrace : WordTrace (prefixWord ++ tailWord_4368823) baseStart_4368823 baseEnd_4368823 := by
    simpa [prefixWord, tailWord_4368823, baseEnd_4368823] using wordTrace_append hprefix tailTrace_4368823
  have hstable : (prefixWord ++ tailWord_4368823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368823).length < 2 ^ (prefixWord ++ tailWord_4368823).sum := by decide
  have hdescent : baseEnd_4368823 < baseStart_4368823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368839 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_4368839 : Nat := 118140960795 + 4368839 * 2 ^ 59
def prefixEnd_4368839 : Nat := 4983230072969 + 3 ^ 40 * 4368839 * 2
def baseEnd_4368839 : Nat := 2243314309108137631020581

theorem tailTrace_4368839 : CollatzResearch.WordTrace tailWord_4368839 prefixEnd_4368839 2243314309108137631020581 := by
  unfold tailWord_4368839
  simp only [CollatzResearch.WordTrace]
  refine ⟨159344649019449916143205571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106229766012966610762137047 159344649019449916143205571)
  ·
    refine ⟨239016973529174874214808357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159344649019449916143205571 239016973529174874214808357)
    ·
      refine ⟨44815682536720288915276567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239016973529174874214808357 44815682536720288915276567)
      ·
        refine ⟨67223523805080433372914851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44815682536720288915276567 67223523805080433372914851)
        ·
          refine ⟨100835285707620650059372277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67223523805080433372914851 100835285707620650059372277)
          ·
            refine ⟨9453308035089435943066151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100835285707620650059372277 9453308035089435943066151)
            ·
              refine ⟨14179962052634153914599227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453308035089435943066151 14179962052634153914599227)
              ·
                refine ⟨21269943078951230871898841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14179962052634153914599227 21269943078951230871898841)
                ·
                  refine ⟨15952457309213423153924131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21269943078951230871898841 15952457309213423153924131)
                  ·
                    refine ⟨23928685963820134730886197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15952457309213423153924131 23928685963820134730886197)
                    ·
                      refine ⟨2243314309108137631020581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23928685963820134730886197 2243314309108137631020581)
                      ·
                        rfl

theorem cell23_4368839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_4368839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368839 prefixEnd_4368839 := by exact prefixLift 4368839
  have htrace : WordTrace (prefixWord ++ tailWord_4368839) baseStart_4368839 baseEnd_4368839 := by
    simpa [prefixWord, tailWord_4368839, baseEnd_4368839] using wordTrace_append hprefix tailTrace_4368839
  have hstable : (prefixWord ++ tailWord_4368839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368839).length < 2 ^ (prefixWord ++ tailWord_4368839).sum := by decide
  have hdescent : baseEnd_4368839 < baseStart_4368839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368853 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4368853 : Nat := 118140960795 + 4368853 * 2 ^ 59
def prefixEnd_4368853 : Nat := 4983230072969 + 3 ^ 40 * 4368853 * 2
def baseEnd_4368853 : Nat := 2243321497837300576245517

theorem tailTrace_4368853 : CollatzResearch.WordTrace tailWord_4368853 prefixEnd_4368853 2243321497837300576245517 := by
  unfold tailWord_4368853
  simp only [CollatzResearch.WordTrace]
  refine ⟨159345159641399196534215213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106230106427599464356143475 159345159641399196534215213)
  ·
    refine ⟨59754434865524698700330705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159345159641399196534215213 59754434865524698700330705)
    ·
      refine ⟨44815826149143524025248029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59754434865524698700330705 44815826149143524025248029)
      ·
        refine ⟨16805934805928821509468011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44815826149143524025248029 16805934805928821509468011)
        ·
          refine ⟨25208902208893232264202017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16805934805928821509468011 25208902208893232264202017)
          ·
            refine ⟨18906676656669924198151513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25208902208893232264202017 18906676656669924198151513)
            ·
              refine ⟨14180007492502443148613635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18906676656669924198151513 14180007492502443148613635)
              ·
                refine ⟨21270011238753664722920453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14180007492502443148613635 21270011238753664722920453)
                ·
                  refine ⟨3988127107266312135547585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21270011238753664722920453 3988127107266312135547585)
                  ·
                    refine ⟨2991095330449734101660689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3988127107266312135547585 2991095330449734101660689)
                    ·
                      refine ⟨2243321497837300576245517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991095330449734101660689 2243321497837300576245517)
                      ·
                        rfl

theorem cell23_4368853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4368853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368853 prefixEnd_4368853 := by exact prefixLift 4368853
  have htrace : WordTrace (prefixWord ++ tailWord_4368853) baseStart_4368853 baseEnd_4368853 := by
    simpa [prefixWord, tailWord_4368853, baseEnd_4368853] using wordTrace_append hprefix tailTrace_4368853
  have hstable : (prefixWord ++ tailWord_4368853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368853).length < 2 ^ (prefixWord ++ tailWord_4368853).sum := by decide
  have hdescent : baseEnd_4368853 < baseStart_4368853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368889 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_4368889 : Nat := 118140960795 + 4368889 * 2 ^ 59
def prefixEnd_4368889 : Nat := 4983230072969 + 3 ^ 40 * 4368889 * 2
def baseEnd_4368889 : Nat := 747779994380287478465117

theorem tailTrace_4368889 : CollatzResearch.WordTrace tailWord_4368889 prefixEnd_4368889 747779994380287478465117 := by
  unfold tailWord_4368889
  simp only [CollatzResearch.WordTrace]
  refine ⟨159346472669268774682525721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106230981779512516455017147 159346472669268774682525721)
  ·
    refine ⟨119509854501951581011894291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159346472669268774682525721 119509854501951581011894291)
    ·
      refine ⟨179264781752927371517841437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119509854501951581011894291 179264781752927371517841437)
      ·
        refine ⟨67224293157347764319190539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179264781752927371517841437 67224293157347764319190539)
        ·
          refine ⟨100836439736021646478785809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67224293157347764319190539 100836439736021646478785809)
          ·
            refine ⟨75627329802016234859089357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100836439736021646478785809 75627329802016234859089357)
            ·
              refine ⟨28360248675756088072158509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75627329802016234859089357 28360248675756088072158509)
              ·
                refine ⟨10635093253408533027059441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28360248675756088072158509 10635093253408533027059441)
                ·
                  refine ⟨7976319940056399770294581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10635093253408533027059441 7976319940056399770294581)
                  ·
                    refine ⟨747779994380287478465117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7976319940056399770294581 747779994380287478465117)
                    ·
                      rfl

theorem cell23_4368889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_4368889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368889 prefixEnd_4368889 := by exact prefixLift 4368889
  have htrace : WordTrace (prefixWord ++ tailWord_4368889) baseStart_4368889 baseEnd_4368889 := by
    simpa [prefixWord, tailWord_4368889, baseEnd_4368889] using wordTrace_append hprefix tailTrace_4368889
  have hstable : (prefixWord ++ tailWord_4368889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368889).length < 2 ^ (prefixWord ++ tailWord_4368889).sum := by decide
  have hdescent : baseEnd_4368889 < baseStart_4368889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368910 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_4368910 : Nat := 118140960795 + 4368910 * 2 ^ 59
def prefixEnd_4368910 : Nat := 4983230072969 + 3 ^ 40 * 4368910 * 2
def baseEnd_4368910 : Nat := 249261196248289650359195

theorem tailTrace_4368910 : CollatzResearch.WordTrace tailWord_4368910 prefixEnd_4368910 249261196248289650359195 := by
  unfold tailWord_4368910
  simp only [CollatzResearch.WordTrace]
  refine ⟨19918404825274086908630023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106231492401461796846026789 19918404825274086908630023)
  ·
    refine ⟨29877607237911130362945035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19918404825274086908630023 29877607237911130362945035)
    ·
      refine ⟨44816410856866695544417553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29877607237911130362945035 44816410856866695544417553)
      ·
        refine ⟨33612308142650021658313165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44816410856866695544417553 33612308142650021658313165)
        ·
          refine ⟨12604615553493758121867437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33612308142650021658313165 12604615553493758121867437)
          ·
            refine ⟨4726730832560159295700289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12604615553493758121867437 4726730832560159295700289)
            ·
              refine ⟨3545048124420119471775217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4726730832560159295700289 3545048124420119471775217)
              ·
                refine ⟨2658786093315089603831413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545048124420119471775217 2658786093315089603831413)
                ·
                  refine ⟨249261196248289650359195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2658786093315089603831413 249261196248289650359195)
                  ·
                    rfl

theorem cell23_4368910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_4368910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368910 prefixEnd_4368910 := by exact prefixLift 4368910
  have htrace : WordTrace (prefixWord ++ tailWord_4368910) baseStart_4368910 baseEnd_4368910 := by
    simpa [prefixWord, tailWord_4368910, baseEnd_4368910] using wordTrace_append hprefix tailTrace_4368910
  have hstable : (prefixWord ++ tailWord_4368910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368910).length < 2 ^ (prefixWord ++ tailWord_4368910).sum := by decide
  have hdescent : baseEnd_4368910 < baseStart_4368910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368949 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 8]
def baseStart_4368949 : Nat := 118140960795 + 4368949 * 2 ^ 59
def prefixEnd_4368949 : Nat := 4983230072969 + 3 ^ 40 * 4368949 * 2
def baseEnd_4368949 : Nat := 249263421331125800071675

theorem tailTrace_4368949 : CollatzResearch.WordTrace tailWord_4368949 prefixEnd_4368949 249263421331125800071675 := by
  unfold tailWord_4368949
  simp only [CollatzResearch.WordTrace]
  refine ⟨159348661049051404929709901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106232440699367603286473267 159348661049051404929709901)
  ·
    refine ⟨59755747893394276848641213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159348661049051404929709901 59755747893394276848641213)
    ·
      refine ⟨22408405460022853818240455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59755747893394276848641213 22408405460022853818240455)
      ·
        refine ⟨33612608190034280727360683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22408405460022853818240455 33612608190034280727360683)
        ·
          refine ⟨50418912285051421091041025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33612608190034280727360683 50418912285051421091041025)
          ·
            refine ⟨37814184213788565818280769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50418912285051421091041025 37814184213788565818280769)
            ·
              refine ⟨28360638160341424363710577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37814184213788565818280769 28360638160341424363710577)
              ·
                refine ⟨21270478620256068272782933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28360638160341424363710577 21270478620256068272782933)
                ·
                  refine ⟨249263421331125800071675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21270478620256068272782933 249263421331125800071675)
                  ·
                    rfl

theorem cell23_4368949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_4368949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368949 prefixEnd_4368949 := by exact prefixLift 4368949
  have htrace : WordTrace (prefixWord ++ tailWord_4368949) baseStart_4368949 baseEnd_4368949 := by
    simpa [prefixWord, tailWord_4368949, baseEnd_4368949] using wordTrace_append hprefix tailTrace_4368949
  have hstable : (prefixWord ++ tailWord_4368949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368949).length < 2 ^ (prefixWord ++ tailWord_4368949).sum := by decide
  have hdescent : baseEnd_4368949 < baseStart_4368949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4368993 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_4368993 : Nat := 118140960795 + 4368993 * 2 ^ 59
def prefixEnd_4368993 : Nat := 4983230072969 + 3 ^ 40 * 4368993 * 2
def baseEnd_4368993 : Nat := 2243393385128930028494873

theorem tailTrace_4368993 : CollatzResearch.WordTrace tailWord_4368993 prefixEnd_4368993 2243393385128930028494873 := by
  unfold tailWord_4368993
  simp only [CollatzResearch.WordTrace]
  refine ⟨159350265860892000444311633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106233510573928000296207755 159350265860892000444311633)
  ·
    refine ⟨119512699395669000333233725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159350265860892000444311633 119512699395669000333233725)
    ·
      refine ⟨44817262273375875124962647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119512699395669000333233725 44817262273375875124962647)
      ·
        refine ⟨67225893410063812687443971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44817262273375875124962647 67225893410063812687443971)
        ·
          refine ⟨100838840115095719031165957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67225893410063812687443971 100838840115095719031165957)
          ·
            refine ⟨18907282521580447318343617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100838840115095719031165957 18907282521580447318343617)
            ·
              refine ⟨14180461891185335488757713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18907282521580447318343617 14180461891185335488757713)
              ·
                refine ⟨10635346418389001616568285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14180461891185335488757713 10635346418389001616568285)
                ·
                  refine ⟨3988254906895875606213107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10635346418389001616568285 3988254906895875606213107)
                  ·
                    refine ⟨5982382360343813409319661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988254906895875606213107 5982382360343813409319661)
                    ·
                      refine ⟨2243393385128930028494873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5982382360343813409319661 2243393385128930028494873)
                      ·
                        rfl

theorem cell23_4368993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_4368993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4368993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4368993 prefixEnd_4368993 := by exact prefixLift 4368993
  have htrace : WordTrace (prefixWord ++ tailWord_4368993) baseStart_4368993 baseEnd_4368993 := by
    simpa [prefixWord, tailWord_4368993, baseEnd_4368993] using wordTrace_append hprefix tailTrace_4368993
  have hstable : (prefixWord ++ tailWord_4368993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4368993).length < 2 ^ (prefixWord ++ tailWord_4368993).sum := by decide
  have hdescent : baseEnd_4368993 < baseStart_4368993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4368993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369016 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_4369016 : Nat := 118140960795 + 4369016 * 2 ^ 59
def prefixEnd_4369016 : Nat := 4983230072969 + 3 ^ 40 * 4369016 * 2
def baseEnd_4369016 : Nat := 2243405195183983438507267

theorem tailTrace_4369016 : CollatzResearch.WordTrace tailWord_4369016 prefixEnd_4369016 2243405195183983438507267 := by
  unfold tailWord_4369016
  simp only [CollatzResearch.WordTrace]
  refine ⟨79675552369904337686199451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106234069826539116914932601 79675552369904337686199451)
  ·
    refine ⟨119513328554856506529299177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79675552369904337686199451 119513328554856506529299177)
    ·
      refine ⟨89634996416142379896974383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119513328554856506529299177 89634996416142379896974383)
      ·
        refine ⟨134452494624213569845461575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89634996416142379896974383 134452494624213569845461575)
        ·
          refine ⟨201678741936320354768192363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134452494624213569845461575 201678741936320354768192363)
          ·
            refine ⟨302518112904480532152288545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201678741936320354768192363 302518112904480532152288545)
            ·
              refine ⟨226888584678360399114216409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302518112904480532152288545 226888584678360399114216409)
              ·
                refine ⟨170166438508770299335662307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226888584678360399114216409 170166438508770299335662307)
                ·
                  refine ⟨255249657763155449003493461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170166438508770299335662307 255249657763155449003493461)
                  ·
                    refine ⟨2991206926911977918009689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 255249657763155449003493461 2991206926911977918009689)
                    ·
                      refine ⟨2243405195183983438507267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991206926911977918009689 2243405195183983438507267)
                      ·
                        rfl

theorem cell23_4369016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_4369016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369016 prefixEnd_4369016 := by exact prefixLift 4369016
  have htrace : WordTrace (prefixWord ++ tailWord_4369016) baseStart_4369016 baseEnd_4369016 := by
    simpa [prefixWord, tailWord_4369016, baseEnd_4369016] using wordTrace_append hprefix tailTrace_4369016
  have hstable : (prefixWord ++ tailWord_4369016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369016).length < 2 ^ (prefixWord ++ tailWord_4369016).sum := by decide
  have hdescent : baseEnd_4369016 < baseStart_4369016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369050 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4369050 : Nat := 118140960795 + 4369050 * 2 ^ 59
def prefixEnd_4369050 : Nat := 4983230072969 + 3 ^ 40 * 4369050 * 2
def baseEnd_4369050 : Nat := 2243422653526236305482111

theorem tailTrace_4369050 : CollatzResearch.WordTrace tailWord_4369050 prefixEnd_4369050 2243422653526236305482111 := by
  unfold tailWord_4369050
  simp only [CollatzResearch.WordTrace]
  refine ⟨39838086205421374794784151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106234896547790332786091069 39838086205421374794784151)
  ·
    refine ⟨59757129308132062192176227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39838086205421374794784151 59757129308132062192176227)
    ·
      refine ⟨89635693962198093288264341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59757129308132062192176227 89635693962198093288264341)
      ·
        refine ⟨4201673154478035622887391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89635693962198093288264341 4201673154478035622887391)
        ·
          refine ⟨6302509731717053434331087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201673154478035622887391 6302509731717053434331087)
          ·
            refine ⟨9453764597575580151496631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302509731717053434331087 9453764597575580151496631)
            ·
              refine ⟨14180646896363370227244947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453764597575580151496631 14180646896363370227244947)
              ·
                refine ⟨21270970344545055340867421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14180646896363370227244947 21270970344545055340867421)
                ·
                  refine ⟨7976613879204395752825283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21270970344545055340867421 7976613879204395752825283)
                  ·
                    refine ⟨11964920818806593629237925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7976613879204395752825283 11964920818806593629237925)
                    ·
                      refine ⟨2243422653526236305482111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11964920818806593629237925 2243422653526236305482111)
                      ·
                        rfl

theorem cell23_4369050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4369050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369050 prefixEnd_4369050 := by exact prefixLift 4369050
  have htrace : WordTrace (prefixWord ++ tailWord_4369050) baseStart_4369050 baseEnd_4369050 := by
    simpa [prefixWord, tailWord_4369050, baseEnd_4369050] using wordTrace_append hprefix tailTrace_4369050
  have hstable : (prefixWord ++ tailWord_4369050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369050).length < 2 ^ (prefixWord ++ tailWord_4369050).sum := by decide
  have hdescent : baseEnd_4369050 < baseStart_4369050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369070 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4369070 : Nat := 118140960795 + 4369070 * 2 ^ 59
def prefixEnd_4369070 : Nat := 4983230072969 + 3 ^ 40 * 4369070 * 2
def baseEnd_4369070 : Nat := 2243432923139326227232019

theorem tailTrace_4369070 : CollatzResearch.WordTrace tailWord_4369070 prefixEnd_4369070 2243432923139326227232019 := by
  unfold tailWord_4369070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919134285201630324358083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106235382854408695063243109 19919134285201630324358083)
  ·
    refine ⟨29878701427802445486537125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19919134285201630324358083 29878701427802445486537125)
    ·
      refine ⟨5602256517712958528725711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29878701427802445486537125 5602256517712958528725711)
      ·
        refine ⟨8403384776569437793088567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602256517712958528725711 8403384776569437793088567)
        ·
          refine ⟨12605077164854156689632851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403384776569437793088567 12605077164854156689632851)
          ·
            refine ⟨18907615747281235034449277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12605077164854156689632851 18907615747281235034449277)
            ·
              refine ⟨7090355905230463137918479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18907615747281235034449277 7090355905230463137918479)
              ·
                refine ⟨10635533857845694706877719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090355905230463137918479 10635533857845694706877719)
                ·
                  refine ⟨15953300786768542060316579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10635533857845694706877719 15953300786768542060316579)
                  ·
                    refine ⟨23929951180152813090474869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15953300786768542060316579 23929951180152813090474869)
                    ·
                      refine ⟨2243432923139326227232019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23929951180152813090474869 2243432923139326227232019)
                      ·
                        rfl

theorem cell23_4369070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4369070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369070 prefixEnd_4369070 := by exact prefixLift 4369070
  have htrace : WordTrace (prefixWord ++ tailWord_4369070) baseStart_4369070 baseEnd_4369070 := by
    simpa [prefixWord, tailWord_4369070, baseEnd_4369070] using wordTrace_append hprefix tailTrace_4369070
  have hstable : (prefixWord ++ tailWord_4369070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369070).length < 2 ^ (prefixWord ++ tailWord_4369070).sum := by decide
  have hdescent : baseEnd_4369070 < baseStart_4369070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369073 : List Nat := [1, 2, 2, 6, 2, 10]
def baseStart_4369073 : Nat := 118140960795 + 4369073 * 2 ^ 59
def prefixEnd_4369073 : Nat := 4983230072969 + 3 ^ 40 * 4369073 * 2
def baseEnd_4369073 : Nat := 9232240590869505002035

theorem tailTrace_4369073 : CollatzResearch.WordTrace tailWord_4369073 prefixEnd_4369073 9232240590869505002035 := by
  unfold tailWord_4369073
  simp only [CollatzResearch.WordTrace]
  refine ⟨159353183700602174107223873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106235455800401449404815915 159353183700602174107223873)
  ·
    refine ⟨119514887775451630580417905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159353183700602174107223873 119514887775451630580417905)
    ·
      refine ⟨89636165831588722935313429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119514887775451630580417905 89636165831588722935313429)
      ·
        refine ⟨4201695273355721387592817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89636165831588722935313429 4201695273355721387592817)
        ·
          refine ⟨3151271455016791040694613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4201695273355721387592817 3151271455016791040694613)
          ·
            refine ⟨9232240590869505002035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3151271455016791040694613 9232240590869505002035)
            ·
              rfl

theorem cell23_4369073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 10].length) (baseStart_4369073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369073 prefixEnd_4369073 := by exact prefixLift 4369073
  have htrace : WordTrace (prefixWord ++ tailWord_4369073) baseStart_4369073 baseEnd_4369073 := by
    simpa [prefixWord, tailWord_4369073, baseEnd_4369073] using wordTrace_append hprefix tailTrace_4369073
  have hstable : (prefixWord ++ tailWord_4369073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369073).length < 2 ^ (prefixWord ++ tailWord_4369073).sum := by decide
  have hdescent : baseEnd_4369073 < baseStart_4369073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369078 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4369078 : Nat := 118140960795 + 4369078 * 2 ^ 59
def prefixEnd_4369078 : Nat := 4983230072969 + 3 ^ 40 * 4369078 * 2
def baseEnd_4369078 : Nat := 2243437030984562195931983

theorem tailTrace_4369078 : CollatzResearch.WordTrace tailWord_4369078 prefixEnd_4369078 2243437030984562195931983 := by
  unfold tailWord_4369078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959585379099003747572243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106235577377056039974103925 9959585379099003747572243)
  ·
    refine ⟨14939378068648505621358365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959585379099003747572243 14939378068648505621358365)
    ·
      refine ⟨5602266775743189608009387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14939378068648505621358365 5602266775743189608009387)
      ·
        refine ⟨8403400163614784412014081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602266775743189608009387 8403400163614784412014081)
        ·
          refine ⟨6302550122711088309010561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8403400163614784412014081 6302550122711088309010561)
          ·
            refine ⟨4726912592033316231757921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6302550122711088309010561 4726912592033316231757921)
            ·
              refine ⟨3545184444024987173818441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4726912592033316231757921 3545184444024987173818441)
              ·
                refine ⟨2658888333018740380363831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545184444024987173818441 2658888333018740380363831)
                ·
                  refine ⟨3988332499528110570545747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2658888333018740380363831 3988332499528110570545747)
                  ·
                    refine ⟨5982498749292165855818621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988332499528110570545747 5982498749292165855818621)
                    ·
                      refine ⟨2243437030984562195931983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5982498749292165855818621 2243437030984562195931983)
                      ·
                        rfl

theorem cell23_4369078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4369078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369078 prefixEnd_4369078 := by exact prefixLift 4369078
  have htrace : WordTrace (prefixWord ++ tailWord_4369078) baseStart_4369078 baseEnd_4369078 := by
    simpa [prefixWord, tailWord_4369078, baseEnd_4369078] using wordTrace_append hprefix tailTrace_4369078
  have hstable : (prefixWord ++ tailWord_4369078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369078).length < 2 ^ (prefixWord ++ tailWord_4369078).sum := by decide
  have hdescent : baseEnd_4369078 < baseStart_4369078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369086 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4369086 : Nat := 118140960795 + 4369086 * 2 ^ 59
def prefixEnd_4369086 : Nat := 4983230072969 + 3 ^ 40 * 4369086 * 2
def baseEnd_4369086 : Nat := 747813712943266054877315

theorem tailTrace_4369086 : CollatzResearch.WordTrace tailWord_4369086 prefixEnd_4369086 747813712943266054877315 := by
  unfold tailWord_4369086
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919207231194384665930889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106235771899703384884964741 19919207231194384665930889)
  ·
    refine ⟨14939405423395788499448167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19919207231194384665930889 14939405423395788499448167)
    ·
      refine ⟨22409108135093682749172251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14939405423395788499448167 22409108135093682749172251)
      ·
        refine ⟨33613662202640524123758377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22409108135093682749172251 33613662202640524123758377)
        ·
          refine ⟨25210246651980393092818783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33613662202640524123758377 25210246651980393092818783)
          ·
            refine ⟨37815369977970589639228175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25210246651980393092818783 37815369977970589639228175)
            ·
              refine ⟨56723054966955884458842263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37815369977970589639228175 56723054966955884458842263)
              ·
                refine ⟨85084582450433826688263395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56723054966955884458842263 85084582450433826688263395)
                ·
                  refine ⟨127626873675650740032395093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85084582450433826688263395 127626873675650740032395093)
                  ·
                    refine ⟨747813712943266054877315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127626873675650740032395093 747813712943266054877315)
                    ·
                      rfl

theorem cell23_4369086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4369086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369086 prefixEnd_4369086 := by exact prefixLift 4369086
  have htrace : WordTrace (prefixWord ++ tailWord_4369086) baseStart_4369086 baseEnd_4369086 := by
    simpa [prefixWord, tailWord_4369086, baseEnd_4369086] using wordTrace_append hprefix tailTrace_4369086
  have hstable : (prefixWord ++ tailWord_4369086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369086).length < 2 ^ (prefixWord ++ tailWord_4369086).sum := by decide
  have hdescent : baseEnd_4369086 < baseStart_4369086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369100 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4369100 : Nat := 118140960795 + 4369100 * 2 ^ 59
def prefixEnd_4369100 : Nat := 4983230072969 + 3 ^ 40 * 4369100 * 2
def baseEnd_4369100 : Nat := 2243448327558961109856881

theorem tailTrace_4369100 : CollatzResearch.WordTrace tailWord_4369100 prefixEnd_4369100 2243448327558961109856881 := by
  unfold tailWord_4369100
  simp only [CollatzResearch.WordTrace]
  refine ⟨79677084235752178859228377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106236112314336238478971169 79677084235752178859228377)
  ·
    refine ⟨59757813176814134144421283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79677084235752178859228377 59757813176814134144421283)
    ·
      refine ⟨89636719765221201216631925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59757813176814134144421283 89636719765221201216631925)
      ·
        refine ⟨8403442477989487614059243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89636719765221201216631925 8403442477989487614059243)
        ·
          refine ⟨12605163716984231421088865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403442477989487614059243 12605163716984231421088865)
          ·
            refine ⟨9453872787738173565816649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605163716984231421088865 9453872787738173565816649)
            ·
              refine ⟨7090404590803630174362487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9453872787738173565816649 7090404590803630174362487)
              ·
                refine ⟨10635606886205445261543731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090404590803630174362487 10635606886205445261543731)
                ·
                  refine ⟨15953410329308167892315597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10635606886205445261543731 15953410329308167892315597)
                  ·
                    refine ⟨5982528873490562959618349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15953410329308167892315597 5982528873490562959618349)
                    ·
                      refine ⟨2243448327558961109856881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5982528873490562959618349 2243448327558961109856881)
                      ·
                        rfl

theorem cell23_4369100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4369100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369100 prefixEnd_4369100 := by exact prefixLift 4369100
  have htrace : WordTrace (prefixWord ++ tailWord_4369100) baseStart_4369100 baseEnd_4369100 := by
    simpa [prefixWord, tailWord_4369100, baseEnd_4369100] using wordTrace_append hprefix tailTrace_4369100
  have hstable : (prefixWord ++ tailWord_4369100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369100).length < 2 ^ (prefixWord ++ tailWord_4369100).sum := by decide
  have hdescent : baseEnd_4369100 < baseStart_4369100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369136 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_4369136 : Nat := 118140960795 + 4369136 * 2 ^ 59
def prefixEnd_4369136 : Nat := 4983230072969 + 3 ^ 40 * 4369136 * 2
def baseEnd_4369136 : Nat := 2243466812862522969006715

theorem tailTrace_4369136 : CollatzResearch.WordTrace tailWord_4369136 prefixEnd_4369136 2243466812862522969006715 := by
  unfold tailWord_4369136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79677740749686967933383631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106236987666249290577844841 79677740749686967933383631)
  ·
    refine ⟨119516611124530451900075447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79677740749686967933383631 119516611124530451900075447)
    ·
      refine ⟨179274916686795677850113171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119516611124530451900075447 179274916686795677850113171)
      ·
        refine ⟨268912375030193516775169757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179274916686795677850113171 268912375030193516775169757)
        ·
          refine ⟨100842140636322568790688659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268912375030193516775169757 100842140636322568790688659)
          ·
            refine ⟨151263210954483853186032989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100842140636322568790688659 151263210954483853186032989)
            ·
              refine ⟨56723704107931444944762371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151263210954483853186032989 56723704107931444944762371)
              ·
                refine ⟨85085556161897167417143557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56723704107931444944762371 85085556161897167417143557)
                ·
                  refine ⟨15953541780355718890714417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85085556161897167417143557 15953541780355718890714417)
                  ·
                    refine ⟨11965156335266789168035813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15953541780355718890714417 11965156335266789168035813)
                    ·
                      refine ⟨2243466812862522969006715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11965156335266789168035813 2243466812862522969006715)
                      ·
                        rfl

theorem cell23_4369136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_4369136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369136 prefixEnd_4369136 := by exact prefixLift 4369136
  have htrace : WordTrace (prefixWord ++ tailWord_4369136) baseStart_4369136 baseEnd_4369136 := by
    simpa [prefixWord, tailWord_4369136, baseEnd_4369136] using wordTrace_append hprefix tailTrace_4369136
  have hstable : (prefixWord ++ tailWord_4369136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369136).length < 2 ^ (prefixWord ++ tailWord_4369136).sum := by decide
  have hdescent : baseEnd_4369136 < baseStart_4369136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369146 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 7]
def baseStart_4369146 : Nat := 118140960795 + 4369146 * 2 ^ 59
def prefixEnd_4369146 : Nat := 4983230072969 + 3 ^ 40 * 4369146 * 2
def baseEnd_4369146 : Nat := 249274660852118658875741

theorem tailTrace_4369146 : CollatzResearch.WordTrace tailWord_4369146 prefixEnd_4369146 249274660852118658875741 := by
  unfold tailWord_4369146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39838961557334426893657823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106237230819558471716420861 39838961557334426893657823)
  ·
    refine ⟨59758442336001640340486735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39838961557334426893657823 59758442336001640340486735)
    ·
      refine ⟨89637663504002460510730103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59758442336001640340486735 89637663504002460510730103)
      ·
        refine ⟨134456495256003690766095155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89637663504002460510730103 134456495256003690766095155)
        ·
          refine ⟨201684742884005536149142733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134456495256003690766095155 201684742884005536149142733)
          ·
            refine ⟨75631778581502076055928525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201684742884005536149142733 75631778581502076055928525)
            ·
              refine ⟨28361916968063278520973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75631778581502076055928525 28361916968063278520973197)
              ·
                refine ⟨10635718863023729445364949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28361916968063278520973197 10635718863023729445364949)
                ·
                  refine ⟨249274660852118658875741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10635718863023729445364949 249274660852118658875741)
                  ·
                    rfl

theorem cell23_4369146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_4369146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369146 prefixEnd_4369146 := by exact prefixLift 4369146
  have htrace : WordTrace (prefixWord ++ tailWord_4369146) baseStart_4369146 baseEnd_4369146 := by
    simpa [prefixWord, tailWord_4369146, baseEnd_4369146] using wordTrace_append hprefix tailTrace_4369146
  have hstable : (prefixWord ++ tailWord_4369146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369146).length < 2 ^ (prefixWord ++ tailWord_4369146).sum := by decide
  have hdescent : baseEnd_4369146 < baseStart_4369146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369180 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 5]
def baseStart_4369180 : Nat := 118140960795 + 4369180 * 2 ^ 59
def prefixEnd_4369180 : Nat := 4983230072969 + 3 ^ 40 * 4369180 * 2
def baseEnd_4369180 : Nat := 249276600667924532984057

theorem tailTrace_4369180 : CollatzResearch.WordTrace tailWord_4369180 prefixEnd_4369180 249276600667924532984057 := by
  unfold tailWord_4369180
  simp only [CollatzResearch.WordTrace]
  refine ⟨79678543155607265690684497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106238057540809687587579329 79678543155607265690684497)
  ·
    refine ⟨59758907366705449268013373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79678543155607265690684497 59758907366705449268013373)
    ·
      refine ⟨22409590262514543475505015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59758907366705449268013373 22409590262514543475505015)
      ·
        refine ⟨33614385393771815213257523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22409590262514543475505015 33614385393771815213257523)
        ·
          refine ⟨50421578090657722819886285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33614385393771815213257523 50421578090657722819886285)
          ·
            refine ⟨18908091783996646057457357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50421578090657722819886285 18908091783996646057457357)
            ·
              refine ⟨7090534418998742271546509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18908091783996646057457357 7090534418998742271546509)
              ·
                refine ⟨2658950407124528351829941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7090534418998742271546509 2658950407124528351829941)
                ·
                  refine ⟨249276600667924532984057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2658950407124528351829941 249276600667924532984057)
                  ·
                    rfl

theorem cell23_4369180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_4369180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369180 prefixEnd_4369180 := by exact prefixLift 4369180
  have htrace : WordTrace (prefixWord ++ tailWord_4369180) baseStart_4369180 baseEnd_4369180 := by
    simpa [prefixWord, tailWord_4369180, baseEnd_4369180] using wordTrace_append hprefix tailTrace_4369180
  have hstable : (prefixWord ++ tailWord_4369180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369180).length < 2 ^ (prefixWord ++ tailWord_4369180).sum := by decide
  have hdescent : baseEnd_4369180 < baseStart_4369180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369203 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5]
def baseStart_4369203 : Nat := 118140960795 + 4369203 * 2 ^ 59
def prefixEnd_4369203 : Nat := 4983230072969 + 3 ^ 40 * 4369203 * 2
def baseEnd_4369203 : Nat := 2243501216066374206868907

theorem tailTrace_4369203 : CollatzResearch.WordTrace tailWord_4369203 prefixEnd_4369203 2243501216066374206868907 := by
  unfold tailWord_4369203
  simp only [CollatzResearch.WordTrace]
  refine ⟨159357925190131206309456263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106238616793420804206304175 159357925190131206309456263)
  ·
    refine ⟨239036887785196809464184395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159357925190131206309456263 239036887785196809464184395)
    ·
      refine ⟨358555331677795214196276593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239036887785196809464184395 358555331677795214196276593)
      ·
        refine ⟨268916498758346410647207445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358555331677795214196276593 268916498758346410647207445)
        ·
          refine ⟨12605460879297487999087849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 268916498758346410647207445 12605460879297487999087849)
          ·
            refine ⟨9454095659473115999315887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605460879297487999087849 9454095659473115999315887)
            ·
              refine ⟨14181143489209673998973831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9454095659473115999315887 14181143489209673998973831)
              ·
                refine ⟨21271715233814510998460747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14181143489209673998973831 21271715233814510998460747)
                ·
                  refine ⟨31907572850721766497691121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21271715233814510998460747 31907572850721766497691121)
                  ·
                    refine ⟨23930679638041324873268341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31907572850721766497691121 23930679638041324873268341)
                    ·
                      refine ⟨2243501216066374206868907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23930679638041324873268341 2243501216066374206868907)
                      ·
                        rfl

theorem cell23_4369203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_4369203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369203 prefixEnd_4369203 := by exact prefixLift 4369203
  have htrace : WordTrace (prefixWord ++ tailWord_4369203) baseStart_4369203 baseEnd_4369203 := by
    simpa [prefixWord, tailWord_4369203, baseEnd_4369203] using wordTrace_append hprefix tailTrace_4369203
  have hstable : (prefixWord ++ tailWord_4369203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369203).length < 2 ^ (prefixWord ++ tailWord_4369203).sum := by decide
  have hdescent : baseEnd_4369203 < baseStart_4369203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369216 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_4369216 : Nat := 118140960795 + 4369216 * 2 ^ 59
def prefixEnd_4369216 : Nat := 4983230072969 + 3 ^ 40 * 4369216 * 2
def baseEnd_4369216 : Nat := 2243507891314882656006347

theorem tailTrace_4369216 : CollatzResearch.WordTrace tailWord_4369216 prefixEnd_4369216 2243507891314882656006347 := by
  unfold tailWord_4369216
  simp only [CollatzResearch.WordTrace]
  refine ⟨79679199669542054764839751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106238932892722739686453001 79679199669542054764839751)
  ·
    refine ⟨119518799504313082147259627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79679199669542054764839751 119518799504313082147259627)
    ·
      refine ⟨179278199256469623220889441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119518799504313082147259627 179278199256469623220889441)
      ·
        refine ⟨134458649442352217415667081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179278199256469623220889441 134458649442352217415667081)
        ·
          refine ⟨100843987081764163061750311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134458649442352217415667081 100843987081764163061750311)
          ·
            refine ⟨151265980622646244592625467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100843987081764163061750311 151265980622646244592625467)
            ·
              refine ⟨226898970933969366888938201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151265980622646244592625467 226898970933969366888938201)
              ·
                refine ⟨170174228200477025166703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226898970933969366888938201 170174228200477025166703651)
                ·
                  refine ⟨255261342300715537750055477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170174228200477025166703651 255261342300715537750055477)
                  ·
                    refine ⟨23930750840692081664067701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255261342300715537750055477 23930750840692081664067701)
                    ·
                      refine ⟨2243507891314882656006347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23930750840692081664067701 2243507891314882656006347)
                      ·
                        rfl

theorem cell23_4369216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_4369216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369216 prefixEnd_4369216 := by exact prefixLift 4369216
  have htrace : WordTrace (prefixWord ++ tailWord_4369216) baseStart_4369216 baseEnd_4369216 := by
    simpa [prefixWord, tailWord_4369216, baseEnd_4369216] using wordTrace_append hprefix tailTrace_4369216
  have hstable : (prefixWord ++ tailWord_4369216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369216).length < 2 ^ (prefixWord ++ tailWord_4369216).sum := by decide
  have hdescent : baseEnd_4369216 < baseStart_4369216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369223 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 5, 4]
def baseStart_4369223 : Nat := 118140960795 + 4369223 * 2 ^ 59
def prefixEnd_4369223 : Nat := 4983230072969 + 3 ^ 40 * 4369223 * 2
def baseEnd_4369223 : Nat := 747837161893154709539605

theorem tailTrace_4369223 : CollatzResearch.WordTrace tailWord_4369223 prefixEnd_4369223 747837161893154709539605 := by
  unfold tailWord_4369223
  simp only [CollatzResearch.WordTrace]
  refine ⟨159358654650058749725184323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106239103100039166483456215 159358654650058749725184323)
  ·
    refine ⟨239037981975088124587776485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159358654650058749725184323 239037981975088124587776485)
    ·
      refine ⟨44819621620329023360208091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239037981975088124587776485 44819621620329023360208091)
      ·
        refine ⟨67229432430493535040312137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44819621620329023360208091 67229432430493535040312137)
        ·
          refine ⟨50422074322870151280234103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67229432430493535040312137 50422074322870151280234103)
          ·
            refine ⟨75633111484305226920351155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50422074322870151280234103 75633111484305226920351155)
            ·
              refine ⟨113449667226457840380526733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75633111484305226920351155 113449667226457840380526733)
              ·
                refine ⟨42543625209921690142697525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113449667226457840380526733 42543625209921690142697525)
                ·
                  refine ⟨3988464863430158450877893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42543625209921690142697525 3988464863430158450877893)
                  ·
                    refine ⟨747837161893154709539605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3988464863430158450877893 747837161893154709539605)
                    ·
                      rfl

theorem cell23_4369223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_4369223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369223 prefixEnd_4369223 := by exact prefixLift 4369223
  have htrace : WordTrace (prefixWord ++ tailWord_4369223) baseStart_4369223 baseEnd_4369223 := by
    simpa [prefixWord, tailWord_4369223, baseEnd_4369223] using wordTrace_append hprefix tailTrace_4369223
  have hstable : (prefixWord ++ tailWord_4369223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369223).length < 2 ^ (prefixWord ++ tailWord_4369223).sum := by decide
  have hdescent : baseEnd_4369223 < baseStart_4369223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369253 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 6]
def baseStart_4369253 : Nat := 118140960795 + 4369253 * 2 ^ 59
def prefixEnd_4369253 : Nat := 4983230072969 + 3 ^ 40 * 4369253 * 2
def baseEnd_4369253 : Nat := 249280765566566556804853

theorem tailTrace_4369253 : CollatzResearch.WordTrace tailWord_4369253 prefixEnd_4369253 249280765566566556804853 := by
  unfold tailWord_4369253
  simp only [CollatzResearch.WordTrace]
  refine ⟨159359748839950064848776413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106239832559966709899184275 159359748839950064848776413)
  ·
    refine ⟨59759905814981274318291155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159359748839950064848776413 59759905814981274318291155)
    ·
      refine ⟨89639858722471911477436733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59759905814981274318291155 89639858722471911477436733)
      ·
        refine ⟨33614947020926966804038775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89639858722471911477436733 33614947020926966804038775)
        ·
          refine ⟨50422420531390450206058163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33614947020926966804038775 50422420531390450206058163)
          ·
            refine ⟨75633630797085675309087245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50422420531390450206058163 75633630797085675309087245)
            ·
              refine ⟨28362611548907128240907717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75633630797085675309087245 28362611548907128240907717)
              ·
                refine ⟨5317989665420086545170197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28362611548907128240907717 5317989665420086545170197)
                ·
                  refine ⟨249280765566566556804853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5317989665420086545170197 249280765566566556804853)
                  ·
                    rfl

theorem cell23_4369253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_4369253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369253 prefixEnd_4369253 := by exact prefixLift 4369253
  have htrace : WordTrace (prefixWord ++ tailWord_4369253) baseStart_4369253 baseEnd_4369253 := by
    simpa [prefixWord, tailWord_4369253, baseEnd_4369253] using wordTrace_append hprefix tailTrace_4369253
  have hstable : (prefixWord ++ tailWord_4369253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369253).length < 2 ^ (prefixWord ++ tailWord_4369253).sum := by decide
  have hdescent : baseEnd_4369253 < baseStart_4369253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369283 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 3, 5]
def baseStart_4369283 : Nat := 118140960795 + 4369283 * 2 ^ 59
def prefixEnd_4369283 : Nat := 4983230072969 + 3 ^ 40 * 4369283 * 2
def baseEnd_4369283 : Nat := 747847431506244631289513

theorem tailTrace_4369283 : CollatzResearch.WordTrace tailWord_4369283 prefixEnd_4369283 747847431506244631289513 := by
  unfold tailWord_4369283
  simp only [CollatzResearch.WordTrace]
  refine ⟨159360843029841379972368503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106240562019894253314912335 159360843029841379972368503)
  ·
    refine ⟨239041264544762069958552755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159360843029841379972368503 239041264544762069958552755)
    ·
      refine ⟨358561896817143104937829133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239041264544762069958552755 358561896817143104937829133)
      ·
        refine ⟨134460711306428664351685925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358561896817143104937829133 134460711306428664351685925)
        ·
          refine ⟨25211383369955374565941111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134460711306428664351685925 25211383369955374565941111)
          ·
            refine ⟨37817075054933061848911667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25211383369955374565941111 37817075054933061848911667)
            ·
              refine ⟨56725612582399592773367501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37817075054933061848911667 56725612582399592773367501)
              ·
                refine ⟨21272104718399847290012813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56725612582399592773367501 21272104718399847290012813)
                ·
                  refine ⟨7977039269399942733754805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21272104718399847290012813 7977039269399942733754805)
                  ·
                    refine ⟨747847431506244631289513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7977039269399942733754805 747847431506244631289513)
                    ·
                      rfl

theorem cell23_4369283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 5].length) (baseStart_4369283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369283 prefixEnd_4369283 := by exact prefixLift 4369283
  have htrace : WordTrace (prefixWord ++ tailWord_4369283) baseStart_4369283 baseEnd_4369283 := by
    simpa [prefixWord, tailWord_4369283, baseEnd_4369283] using wordTrace_append hprefix tailTrace_4369283
  have hstable : (prefixWord ++ tailWord_4369283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369283).length < 2 ^ (prefixWord ++ tailWord_4369283).sum := by decide
  have hdescent : baseEnd_4369283 < baseStart_4369283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369314 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4369314 : Nat := 118140960795 + 4369314 * 2 ^ 59
def prefixEnd_4369314 : Nat := 4983230072969 + 3 ^ 40 * 4369314 * 2
def baseEnd_4369314 : Nat := 2243558212419023272580897

theorem tailTrace_4369314 : CollatzResearch.WordTrace tailWord_4369314 prefixEnd_4369314 2243558212419023272580897 := by
  unfold tailWord_4369314
  simp only [CollatzResearch.WordTrace]
  refine ⟨39840493423182268066686749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106241315795152714844497997 39840493423182268066686749)
  ·
    refine ⟨14940185033693350525007531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39840493423182268066686749 14940185033693350525007531)
    ·
      refine ⟨22410277550540025787511297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14940185033693350525007531 22410277550540025787511297)
      ·
        refine ⟨16807708162905019340633473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22410277550540025787511297 16807708162905019340633473)
        ·
          refine ⟨12605781122178764505475105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16807708162905019340633473 12605781122178764505475105)
          ·
            refine ⟨9454335841634073379106329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605781122178764505475105 9454335841634073379106329)
            ·
              refine ⟨7090751881225555034329747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454335841634073379106329 7090751881225555034329747)
              ·
                refine ⟨10636127821838332551494621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090751881225555034329747 10636127821838332551494621)
                ·
                  refine ⟨3988547933189374706810483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10636127821838332551494621 3988547933189374706810483)
                  ·
                    refine ⟨5982821899784062060215725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988547933189374706810483 5982821899784062060215725)
                    ·
                      refine ⟨2243558212419023272580897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5982821899784062060215725 2243558212419023272580897)
                      ·
                        rfl

theorem cell23_4369314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4369314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369314 prefixEnd_4369314 := by exact prefixLift 4369314
  have htrace : WordTrace (prefixWord ++ tailWord_4369314) baseStart_4369314 baseEnd_4369314 := by
    simpa [prefixWord, tailWord_4369314, baseEnd_4369314] using wordTrace_append hprefix tailTrace_4369314
  have hstable : (prefixWord ++ tailWord_4369314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369314).length < 2 ^ (prefixWord ++ tailWord_4369314).sum := by decide
  have hdescent : baseEnd_4369314 < baseStart_4369314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5]
def baseStart_4369323 : Nat := 118140960795 + 4369323 * 2 ^ 59
def prefixEnd_4369323 : Nat := 4983230072969 + 3 ^ 40 * 4369323 * 2
def baseEnd_4369323 : Nat := 2243562833744913737368355

theorem tailTrace_4369323 : CollatzResearch.WordTrace tailWord_4369323 prefixEnd_4369323 2243562833744913737368355 := by
  unfold tailWord_4369323
  simp only [CollatzResearch.WordTrace]
  refine ⟨159362301949696466803824623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106241534633130977869216415 159362301949696466803824623)
  ·
    refine ⟨239043452924544700205736935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159362301949696466803824623 239043452924544700205736935)
    ·
      refine ⟨358565179386817050308605403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239043452924544700205736935 358565179386817050308605403)
      ·
        refine ⟨537847769080225575462908105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358565179386817050308605403 537847769080225575462908105)
        ·
          refine ⟨403385826810169181597181079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 537847769080225575462908105 403385826810169181597181079)
          ·
            refine ⟨605078740215253772395771619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403385826810169181597181079 605078740215253772395771619)
            ·
              refine ⟨907618110322880658593657429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605078740215253772395771619 907618110322880658593657429)
              ·
                refine ⟨10636149730346257717894423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 907618110322880658593657429 10636149730346257717894423)
                ·
                  refine ⟨15954224595519386576841635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10636149730346257717894423 15954224595519386576841635)
                  ·
                    refine ⟨23931336893279079865262453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15954224595519386576841635 23931336893279079865262453)
                    ·
                      refine ⟨2243562833744913737368355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23931336893279079865262453 2243562833744913737368355)
                      ·
                        rfl

theorem cell23_4369323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 5].length) (baseStart_4369323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369323 prefixEnd_4369323 := by exact prefixLift 4369323
  have htrace : WordTrace (prefixWord ++ tailWord_4369323) baseStart_4369323 baseEnd_4369323 := by
    simpa [prefixWord, tailWord_4369323, baseEnd_4369323] using wordTrace_append hprefix tailTrace_4369323
  have hstable : (prefixWord ++ tailWord_4369323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369323).length < 2 ^ (prefixWord ++ tailWord_4369323).sum := by decide
  have hdescent : baseEnd_4369323 < baseStart_4369323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369337 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4369337 : Nat := 118140960795 + 4369337 * 2 ^ 59
def prefixEnd_4369337 : Nat := 4983230072969 + 3 ^ 40 * 4369337 * 2
def baseEnd_4369337 : Nat := 2243570022474076682593291

theorem tailTrace_4369337 : CollatzResearch.WordTrace tailWord_4369337 prefixEnd_4369337 2243570022474076682593291 := by
  unfold tailWord_4369337
  simp only [CollatzResearch.WordTrace]
  refine ⟨159362812571645747194834265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106241875047763831463222843 159362812571645747194834265)
  ·
    refine ⟨119522109428734310396125699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159362812571645747194834265 119522109428734310396125699)
    ·
      refine ⟨179283164143101465594188549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119522109428734310396125699 179283164143101465594188549)
      ·
        refine ⟨33615593276831524798910353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179283164143101465594188549 33615593276831524798910353)
        ·
          refine ⟨25211694957623643599182765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33615593276831524798910353 25211694957623643599182765)
          ·
            refine ⟨9454385609108866349693537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25211694957623643599182765 9454385609108866349693537)
            ·
              refine ⟨7090789206831649762270153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454385609108866349693537 7090789206831649762270153)
              ·
                refine ⟨5318091905123737321702615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7090789206831649762270153 5318091905123737321702615)
                ·
                  refine ⟨7977137857685605982553923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5318091905123737321702615 7977137857685605982553923)
                  ·
                    refine ⟨11965706786528408973830885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7977137857685605982553923 11965706786528408973830885)
                    ·
                      refine ⟨2243570022474076682593291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11965706786528408973830885 2243570022474076682593291)
                      ·
                        rfl

theorem cell23_4369337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4369337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369337 prefixEnd_4369337 := by exact prefixLift 4369337
  have htrace : WordTrace (prefixWord ++ tailWord_4369337) baseStart_4369337 baseEnd_4369337 := by
    simpa [prefixWord, tailWord_4369337, baseEnd_4369337] using wordTrace_append hprefix tailTrace_4369337
  have hstable : (prefixWord ++ tailWord_4369337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369337).length < 2 ^ (prefixWord ++ tailWord_4369337).sum := by decide
  have hdescent : baseEnd_4369337 < baseStart_4369337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369403 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 4, 6]
def baseStart_4369403 : Nat := 118140960795 + 4369403 * 2 ^ 59
def prefixEnd_4369403 : Nat := 4983230072969 + 3 ^ 40 * 4369403 * 2
def baseEnd_4369403 : Nat := 747867970732424474789329

theorem tailTrace_4369403 : CollatzResearch.WordTrace tailWord_4369403 prefixEnd_4369403 747867970732424474789329 := by
  unfold tailWord_4369403
  simp only [CollatzResearch.WordTrace]
  refine ⟨159365219789406640466736863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106243479859604426977824575 159365219789406640466736863)
  ·
    refine ⟨239047829684109960700105295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159365219789406640466736863 239047829684109960700105295)
    ·
      refine ⟨358571744526164941050157943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239047829684109960700105295 358571744526164941050157943)
      ·
        refine ⟨537857616789247411575236915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358571744526164941050157943 537857616789247411575236915)
        ·
          refine ⟨806786425183871117362855373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537857616789247411575236915 806786425183871117362855373)
          ·
            refine ⟨302544909443951669011070765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806786425183871117362855373 302544909443951669011070765)
            ·
              refine ⟨113454341041481875879151537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302544909443951669011070765 113454341041481875879151537)
              ·
                refine ⟨85090755781111406909363653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113454341041481875879151537 85090755781111406909363653)
                ·
                  refine ⟨15954516708958388795505685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85090755781111406909363653 15954516708958388795505685)
                  ·
                    refine ⟨747867970732424474789329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15954516708958388795505685 747867970732424474789329)
                    ·
                      rfl

theorem cell23_4369403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 6].length) (baseStart_4369403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369403 prefixEnd_4369403 := by exact prefixLift 4369403
  have htrace : WordTrace (prefixWord ++ tailWord_4369403) baseStart_4369403 baseEnd_4369403 := by
    simpa [prefixWord, tailWord_4369403, baseEnd_4369403] using wordTrace_append hprefix tailTrace_4369403
  have hstable : (prefixWord ++ tailWord_4369403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369403).length < 2 ^ (prefixWord ++ tailWord_4369403).sum := by decide
  have hdescent : baseEnd_4369403 < baseStart_4369403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369437 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_4369437 : Nat := 118140960795 + 4369437 * 2 ^ 59
def prefixEnd_4369437 : Nat := 4983230072969 + 3 ^ 40 * 4369437 * 2
def baseEnd_4369437 : Nat := 747873790179842097114277

theorem tailTrace_4369437 : CollatzResearch.WordTrace tailWord_4369437 prefixEnd_4369437 747873790179842097114277 := by
  unfold tailWord_4369437
  simp only [CollatzResearch.WordTrace]
  refine ⟨159366459871283464273474565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106244306580855642848983043 159366459871283464273474565)
  ·
    refine ⟨29881211225865649551276481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159366459871283464273474565 29881211225865649551276481)
    ·
      refine ⟨22410908419399237163457361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29881211225865649551276481 22410908419399237163457361)
      ·
        refine ⟨16808181314549427872593021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22410908419399237163457361 16808181314549427872593021)
        ·
          refine ⟨6303067992956035452222383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16808181314549427872593021 6303067992956035452222383)
          ·
            refine ⟨9454601989434053178333575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303067992956035452222383 9454601989434053178333575)
            ·
              refine ⟨14181902984151079767500363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9454601989434053178333575 14181902984151079767500363)
              ·
                refine ⟨21272854476226619651250545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14181902984151079767500363 21272854476226619651250545)
                ·
                  refine ⟨15954640857169964738437909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21272854476226619651250545 15954640857169964738437909)
                  ·
                    refine ⟨747873790179842097114277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15954640857169964738437909 747873790179842097114277)
                    ·
                      rfl

theorem cell23_4369437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_4369437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369437 prefixEnd_4369437 := by exact prefixLift 4369437
  have htrace : WordTrace (prefixWord ++ tailWord_4369437) baseStart_4369437 baseEnd_4369437 := by
    simpa [prefixWord, tailWord_4369437, baseEnd_4369437] using wordTrace_append hprefix tailTrace_4369437
  have hstable : (prefixWord ++ tailWord_4369437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369437).length < 2 ^ (prefixWord ++ tailWord_4369437).sum := by decide
  have hdescent : baseEnd_4369437 < baseStart_4369437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
