import V185TrunkScan23Chunk1097

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6501257 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_6501257 : Nat := 118140960795 + 6501257 * 2 ^ 59
def prefixEnd_6501257 : Nat := 4983230072969 + 3 ^ 40 * 6501257 * 2
def baseEnd_6501257 : Nat := 3338269699407375535788769

theorem tailTrace_6501257 : CollatzResearch.WordTrace tailWord_6501257 prefixEnd_6501257 3338269699407375535788769 := by
  unfold tailWord_6501257
  simp only [CollatzResearch.WordTrace]
  refine ⟨237120323008063690143118025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158080215338709126762078683 237120323008063690143118025)
  ·
    refine ⟨177840242256047767607338519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237120323008063690143118025 177840242256047767607338519)
    ·
      refine ⟨266760363384071651411007779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177840242256047767607338519 266760363384071651411007779)
      ·
        refine ⟨400140545076107477116511669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266760363384071651411007779 400140545076107477116511669)
        ·
          refine ⟨37513176100885075979672969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400140545076107477116511669 37513176100885075979672969)
          ·
            refine ⟨28134882075663806984754727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37513176100885075979672969 28134882075663806984754727)
            ·
              refine ⟨42202323113495710477132091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28134882075663806984754727 42202323113495710477132091)
              ·
                refine ⟨63303484670243565715698137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42202323113495710477132091 63303484670243565715698137)
                ·
                  refine ⟨47477613502682674286773603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63303484670243565715698137 47477613502682674286773603)
                  ·
                    refine ⟨71216420254024011430160405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47477613502682674286773603 71216420254024011430160405)
                    ·
                      refine ⟨3338269699407375535788769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71216420254024011430160405 3338269699407375535788769)
                      ·
                        rfl

theorem cell23_6501257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_6501257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501257 prefixEnd_6501257 := by exact prefixLift 6501257
  have htrace : WordTrace (prefixWord ++ tailWord_6501257) baseStart_6501257 baseEnd_6501257 := by
    simpa [prefixWord, tailWord_6501257, baseEnd_6501257] using wordTrace_append hprefix tailTrace_6501257
  have hstable : (prefixWord ++ tailWord_6501257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501257).length < 2 ^ (prefixWord ++ tailWord_6501257).sum := by decide
  have hdescent : baseEnd_6501257 < baseStart_6501257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501267 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 6]
def baseStart_6501267 : Nat := 118140960795 + 6501267 * 2 ^ 59
def prefixEnd_6501267 : Nat := 4983230072969 + 3 ^ 40 * 6501267 * 2
def baseEnd_6501267 : Nat := 370919426023768944073747

theorem tailTrace_6501267 : CollatzResearch.WordTrace tailWord_6501267 prefixEnd_6501267 370919426023768944073747 := by
  unfold tailWord_6501267
  simp only [CollatzResearch.WordTrace]
  refine ⟨237120687738027461850982055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158080458492018307900654703 237120687738027461850982055)
  ·
    refine ⟨355681031607041192776473083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237120687738027461850982055 355681031607041192776473083)
    ·
      refine ⟨533521547410561789164709625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355681031607041192776473083 533521547410561789164709625)
      ·
        refine ⟨400141160557921341873532219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533521547410561789164709625 400141160557921341873532219)
        ·
          refine ⟨600211740836882012810298329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400141160557921341873532219 600211740836882012810298329)
          ·
            refine ⟨450158805627661509607723747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600211740836882012810298329 450158805627661509607723747)
            ·
              refine ⟨675238208441492264411585621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450158805627661509607723747 675238208441492264411585621)
              ·
                refine ⟨7912947755173737473573269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 675238208441492264411585621 7912947755173737473573269)
                ·
                  refine ⟨370919426023768944073747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7912947755173737473573269 370919426023768944073747)
                  ·
                    rfl

theorem cell23_6501267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 6].length) (baseStart_6501267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501267 prefixEnd_6501267 := by exact prefixLift 6501267
  have htrace : WordTrace (prefixWord ++ tailWord_6501267) baseStart_6501267 baseEnd_6501267 := by
    simpa [prefixWord, tailWord_6501267, baseEnd_6501267] using wordTrace_append hprefix tailTrace_6501267
  have hstable : (prefixWord ++ tailWord_6501267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501267).length < 2 ^ (prefixWord ++ tailWord_6501267).sum := by decide
  have hdescent : baseEnd_6501267 < baseStart_6501267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501271 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 1, 4]
def baseStart_6501271 : Nat := 118140960795 + 6501271 * 2 ^ 59
def prefixEnd_6501271 : Nat := 4983230072969 + 3 ^ 40 * 6501271 * 2
def baseEnd_6501271 : Nat := 1112758962712179493671235

theorem tailTrace_6501271 : CollatzResearch.WordTrace tailWord_6501271 prefixEnd_6501271 1112758962712179493671235 := by
  unfold tailWord_6501271
  simp only [CollatzResearch.WordTrace]
  refine ⟨237120833630012970534127667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158080555753341980356085111 237120833630012970534127667)
  ·
    refine ⟨355681250445019455801191501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237120833630012970534127667 355681250445019455801191501)
    ·
      refine ⟨133380468916882295925446813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355681250445019455801191501 133380468916882295925446813)
      ·
        refine ⟨50017675843830860972042555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133380468916882295925446813 50017675843830860972042555)
        ·
          refine ⟨75026513765746291458063833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50017675843830860972042555 75026513765746291458063833)
          ·
            refine ⟨56269885324309718593547875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75026513765746291458063833 56269885324309718593547875)
            ·
              refine ⟨84404827986464577890321813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56269885324309718593547875 84404827986464577890321813)
              ·
                refine ⟨3956476311865527088608835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84404827986464577890321813 3956476311865527088608835)
                ·
                  refine ⟨5934714467798290632913253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956476311865527088608835 5934714467798290632913253)
                  ·
                    refine ⟨1112758962712179493671235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5934714467798290632913253 1112758962712179493671235)
                    ·
                      rfl

theorem cell23_6501271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_6501271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501271 prefixEnd_6501271 := by exact prefixLift 6501271
  have htrace : WordTrace (prefixWord ++ tailWord_6501271) baseStart_6501271 baseEnd_6501271 := by
    simpa [prefixWord, tailWord_6501271, baseEnd_6501271] using wordTrace_append hprefix tailTrace_6501271
  have hstable : (prefixWord ++ tailWord_6501271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501271).length < 2 ^ (prefixWord ++ tailWord_6501271).sum := by decide
  have hdescent : baseEnd_6501271 < baseStart_6501271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501317 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_6501317 : Nat := 118140960795 + 6501317 * 2 ^ 59
def prefixEnd_6501317 : Nat := 4983230072969 + 3 ^ 40 * 6501317 * 2
def baseEnd_6501317 : Nat := 3338300508246645301038493

theorem tailTrace_6501317 : CollatzResearch.WordTrace tailWord_6501317 prefixEnd_6501317 3338300508246645301038493 := by
  unfold tailWord_6501317
  simp only [CollatzResearch.WordTrace]
  refine ⟨237122511387846320390302205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158081674258564213593534803 237122511387846320390302205)
  ·
    refine ⟨88920941770442370146363327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237122511387846320390302205 88920941770442370146363327)
    ·
      refine ⟨133381412655663555219544991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88920941770442370146363327 133381412655663555219544991)
      ·
        refine ⟨200072118983495332829317487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133381412655663555219544991 200072118983495332829317487)
        ·
          refine ⟨300108178475242999243976231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200072118983495332829317487 300108178475242999243976231)
          ·
            refine ⟨450162267712864498865964347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300108178475242999243976231 450162267712864498865964347)
            ·
              refine ⟨675243401569296748298946521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450162267712864498865964347 675243401569296748298946521)
              ·
                refine ⟨506432551176972561224209891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675243401569296748298946521 506432551176972561224209891)
                ·
                  refine ⟨759648826765458841836314837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506432551176972561224209891 759648826765458841836314837)
                  ·
                    refine ⟨17804269377315441605538629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 759648826765458841836314837 17804269377315441605538629)
                    ·
                      refine ⟨3338300508246645301038493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17804269377315441605538629 3338300508246645301038493)
                      ·
                        rfl

theorem cell23_6501317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_6501317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501317 prefixEnd_6501317 := by exact prefixLift 6501317
  have htrace : WordTrace (prefixWord ++ tailWord_6501317) baseStart_6501317 baseEnd_6501317 := by
    simpa [prefixWord, tailWord_6501317, baseEnd_6501317] using wordTrace_append hprefix tailTrace_6501317
  have hstable : (prefixWord ++ tailWord_6501317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501317).length < 2 ^ (prefixWord ++ tailWord_6501317).sum := by decide
  have hdescent : baseEnd_6501317 < baseStart_6501317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501351 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6501351 : Nat := 118140960795 + 6501351 * 2 ^ 59
def prefixEnd_6501351 : Nat := 4983230072969 + 3 ^ 40 * 6501351 * 2
def baseEnd_6501351 : Nat := 3338317966588898168013337

theorem tailTrace_6501351 : CollatzResearch.WordTrace tailWord_6501351 prefixEnd_6501351 3338317966588898168013337 := by
  unfold tailWord_6501351
  simp only [CollatzResearch.WordTrace]
  refine ⟨237123751469723144197039907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158082500979815429464693271 237123751469723144197039907)
  ·
    refine ⟨355685627204584716295559861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237123751469723144197039907 355685627204584716295559861)
    ·
      refine ⟨33345527550429817152708737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355685627204584716295559861 33345527550429817152708737)
      ·
        refine ⟨25009145662822362864531553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33345527550429817152708737 25009145662822362864531553)
        ·
          refine ⟨18756859247116772148398665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25009145662822362864531553 18756859247116772148398665)
          ·
            refine ⟨14067644435337579111298999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18756859247116772148398665 14067644435337579111298999)
            ·
              refine ⟨21101466653006368666948499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14067644435337579111298999 21101466653006368666948499)
              ·
                refine ⟨31652199979509553000422749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21101466653006368666948499 31652199979509553000422749)
                ·
                  refine ⟨11869574992316082375158531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31652199979509553000422749 11869574992316082375158531)
                  ·
                    refine ⟨17804362488474123562737797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11869574992316082375158531 17804362488474123562737797)
                    ·
                      refine ⟨3338317966588898168013337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17804362488474123562737797 3338317966588898168013337)
                      ·
                        rfl

theorem cell23_6501351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6501351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501351 prefixEnd_6501351 := by exact prefixLift 6501351
  have htrace : WordTrace (prefixWord ++ tailWord_6501351) baseStart_6501351 baseEnd_6501351 := by
    simpa [prefixWord, tailWord_6501351, baseEnd_6501351] using wordTrace_append hprefix tailTrace_6501351
  have hstable : (prefixWord ++ tailWord_6501351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501351).length < 2 ^ (prefixWord ++ tailWord_6501351).sum := by decide
  have hdescent : baseEnd_6501351 < baseStart_6501351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501374 : List Nat := [4, 2, 2, 2, 13]
def baseStart_6501374 : Nat := 118140960795 + 6501374 * 2 ^ 59
def prefixEnd_6501374 : Nat := 4983230072969 + 3 ^ 40 * 6501374 * 2
def baseEnd_6501374 : Nat := 4579327539977985703739

theorem tailTrace_6501374 : CollatzResearch.WordTrace tailWord_6501374 prefixEnd_6501374 4579327539977985703739 := by
  unfold tailWord_6501374
  simp only [CollatzResearch.WordTrace]
  refine ⟨29640573793579977390640897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158083060232426546083418117 29640573793579977390640897)
  ·
    refine ⟨22230430345184983042980673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29640573793579977390640897 22230430345184983042980673)
    ·
      refine ⟨16672822758888737282235505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22230430345184983042980673 16672822758888737282235505)
      ·
        refine ⟨12504617069166552961676629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16672822758888737282235505 12504617069166552961676629)
        ·
          refine ⟨4579327539977985703739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12504617069166552961676629 4579327539977985703739)
          ·
            rfl

theorem cell23_6501374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 13].length) (baseStart_6501374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501374 prefixEnd_6501374 := by exact prefixLift 6501374
  have htrace : WordTrace (prefixWord ++ tailWord_6501374) baseStart_6501374 baseEnd_6501374 := by
    simpa [prefixWord, tailWord_6501374, baseEnd_6501374] using wordTrace_append hprefix tailTrace_6501374
  have hstable : (prefixWord ++ tailWord_6501374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501374).length < 2 ^ (prefixWord ++ tailWord_6501374).sum := by decide
  have hdescent : baseEnd_6501374 < baseStart_6501374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501408 : List Nat := [2, 1, 1, 7, 1, 1, 3, 7]
def baseStart_6501408 : Nat := 118140960795 + 6501408 * 2 ^ 59
def prefixEnd_6501408 : Nat := 4983230072969 + 3 ^ 40 * 6501408 * 2
def baseEnd_6501408 : Nat := 123642490184674238703725

theorem tailTrace_6501408 : CollatzResearch.WordTrace tailWord_6501408 prefixEnd_6501408 123642490184674238703725 := by
  unfold tailWord_6501408
  simp only [CollatzResearch.WordTrace]
  refine ⟨118562915215258321465932439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158083886953677761954576585 118562915215258321465932439)
  ·
    refine ⟨177844372822887482198898659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118562915215258321465932439 177844372822887482198898659)
    ·
      refine ⟨266766559234331223298347989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177844372822887482198898659 266766559234331223298347989)
      ·
        refine ⟨6252341232054638046055031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 266766559234331223298347989 6252341232054638046055031)
        ·
          refine ⟨9378511848081957069082547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252341232054638046055031 9378511848081957069082547)
          ·
            refine ⟨14067767772122935603623821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378511848081957069082547 14067767772122935603623821)
            ·
              refine ⟨5275412914546100851358933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14067767772122935603623821 5275412914546100851358933)
              ·
                refine ⟨123642490184674238703725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5275412914546100851358933 123642490184674238703725)
                ·
                  rfl

theorem cell23_6501408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 7].length) (baseStart_6501408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501408 prefixEnd_6501408 := by exact prefixLift 6501408
  have htrace : WordTrace (prefixWord ++ tailWord_6501408) baseStart_6501408 baseEnd_6501408 := by
    simpa [prefixWord, tailWord_6501408, baseEnd_6501408] using wordTrace_append hprefix tailTrace_6501408
  have hstable : (prefixWord ++ tailWord_6501408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501408).length < 2 ^ (prefixWord ++ tailWord_6501408).sum := by decide
  have hdescent : baseEnd_6501408 < baseStart_6501408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501434 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_6501434 : Nat := 118140960795 + 6501434 * 2 ^ 59
def prefixEnd_6501434 : Nat := 4983230072969 + 3 ^ 40 * 6501434 * 2
def baseEnd_6501434 : Nat := 1112786861827740447758485

theorem tailTrace_6501434 : CollatzResearch.WordTrace tailWord_6501434 prefixEnd_6501434 1112786861827740447758485 := by
  unfold tailWord_6501434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59281694682105612343077839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158084519152281632914874237 59281694682105612343077839)
  ·
    refine ⟨88922542023158418514616759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59281694682105612343077839 88922542023158418514616759)
    ·
      refine ⟨133383813034737627771925139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88922542023158418514616759 133383813034737627771925139)
      ·
        refine ⟨200075719552106441657887709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133383813034737627771925139 200075719552106441657887709)
        ·
          refine ⟨75028394832039915621707891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200075719552106441657887709 75028394832039915621707891)
          ·
            refine ⟨112542592248059873432561837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75028394832039915621707891 112542592248059873432561837)
            ·
              refine ⟨42203472093022452537210689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112542592248059873432561837 42203472093022452537210689)
              ·
                refine ⟨31652604069766839402908017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42203472093022452537210689 31652604069766839402908017)
                ·
                  refine ⟨23739453052325129552181013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31652604069766839402908017 23739453052325129552181013)
                  ·
                    refine ⟨1112786861827740447758485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23739453052325129552181013 1112786861827740447758485)
                    ·
                      rfl

theorem cell23_6501434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_6501434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501434 prefixEnd_6501434 := by exact prefixLift 6501434
  have htrace : WordTrace (prefixWord ++ tailWord_6501434) baseStart_6501434 baseEnd_6501434 := by
    simpa [prefixWord, tailWord_6501434, baseEnd_6501434] using wordTrace_append hprefix tailTrace_6501434
  have hstable : (prefixWord ++ tailWord_6501434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501434).length < 2 ^ (prefixWord ++ tailWord_6501434).sum := by decide
  have hdescent : baseEnd_6501434 < baseStart_6501434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501464 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 7]
def baseStart_6501464 : Nat := 118140960795 + 6501464 * 2 ^ 59
def prefixEnd_6501464 : Nat := 4983230072969 + 3 ^ 40 * 6501464 * 2
def baseEnd_6501464 : Nat := 370930665544761802877813

theorem tailTrace_6501464 : CollatzResearch.WordTrace tailWord_6501464 prefixEnd_6501464 370930665544761802877813 := by
  unfold tailWord_6501464
  simp only [CollatzResearch.WordTrace]
  refine ⟨118563936459156882247951723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158085248612209176330602297 118563936459156882247951723)
  ·
    refine ⟨177845904688735323371927585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118563936459156882247951723 177845904688735323371927585)
    ·
      refine ⟨133384428516551492528945689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177845904688735323371927585 133384428516551492528945689)
      ·
        refine ⟨100038321387413619396709267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133384428516551492528945689 100038321387413619396709267)
        ·
          refine ⟨150057482081120429095063901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100038321387413619396709267 150057482081120429095063901)
          ·
            refine ⟨56271555780420160910648963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150057482081120429095063901 56271555780420160910648963)
            ·
              refine ⟨84407333670630241365973445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56271555780420160910648963 84407333670630241365973445)
              ·
                refine ⟨15826375063243170256120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84407333670630241365973445 15826375063243170256120021)
                ·
                  refine ⟨370930665544761802877813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15826375063243170256120021 370930665544761802877813)
                  ·
                    rfl

theorem cell23_6501464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_6501464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501464 prefixEnd_6501464 := by exact prefixLift 6501464
  have htrace : WordTrace (prefixWord ++ tailWord_6501464) baseStart_6501464 baseEnd_6501464 := by
    simpa [prefixWord, tailWord_6501464, baseEnd_6501464] using wordTrace_append hprefix tailTrace_6501464
  have hstable : (prefixWord ++ tailWord_6501464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501464).length < 2 ^ (prefixWord ++ tailWord_6501464).sum := by decide
  have hdescent : baseEnd_6501464 < baseStart_6501464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501504 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_6501504 : Nat := 118140960795 + 6501504 * 2 ^ 59
def prefixEnd_6501504 : Nat := 4983230072969 + 3 ^ 40 * 6501504 * 2
def baseEnd_6501504 : Nat := 3338396529129036069400133

theorem tailTrace_6501504 : CollatzResearch.WordTrace tailWord_6501504 prefixEnd_6501504 3338396529129036069400133 := by
  unfold tailWord_6501504
  simp only [CollatzResearch.WordTrace]
  refine ⟨118564665919084425663679783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158086221225445900884906377 118564665919084425663679783)
  ·
    refine ⟨177846998878626638495519675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118564665919084425663679783 177846998878626638495519675)
    ·
      refine ⟨266770498317939957743279513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177846998878626638495519675 266770498317939957743279513)
      ·
        refine ⟨200077873738454968307459635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266770498317939957743279513 200077873738454968307459635)
        ·
          refine ⟨300116810607682452461189453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200077873738454968307459635 300116810607682452461189453)
          ·
            refine ⟨112543803977880919672946045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300116810607682452461189453 112543803977880919672946045)
            ·
              refine ⟨42203926491705344877354767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112543803977880919672946045 42203926491705344877354767)
              ·
                refine ⟨63305889737558017316032151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42203926491705344877354767 63305889737558017316032151)
                ·
                  refine ⟨94958834606337025974048227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63305889737558017316032151 94958834606337025974048227)
                  ·
                    refine ⟨142438251909505538961072341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94958834606337025974048227 142438251909505538961072341)
                    ·
                      refine ⟨3338396529129036069400133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142438251909505538961072341 3338396529129036069400133)
                      ·
                        rfl

theorem cell23_6501504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_6501504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501504 prefixEnd_6501504 := by exact prefixLift 6501504
  have htrace : WordTrace (prefixWord ++ tailWord_6501504) baseStart_6501504 baseEnd_6501504 := by
    simpa [prefixWord, tailWord_6501504, baseEnd_6501504] using wordTrace_append hprefix tailTrace_6501504
  have hstable : (prefixWord ++ tailWord_6501504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501504).length < 2 ^ (prefixWord ++ tailWord_6501504).sum := by decide
  have hdescent : baseEnd_6501504 < baseStart_6501504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501509 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_6501509 : Nat := 118140960795 + 6501509 * 2 ^ 59
def prefixEnd_6501509 : Nat := 4983230072969 + 3 ^ 40 * 6501509 * 2
def baseEnd_6501509 : Nat := 3338399096532308549837611

theorem tailTrace_6501509 : CollatzResearch.WordTrace tailWord_6501509 prefixEnd_6501509 3338399096532308549837611 := by
  unfold tailWord_6501509
  simp only [CollatzResearch.WordTrace]
  refine ⟨237129514203150737181291581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158086342802100491454194387 237129514203150737181291581)
  ·
    refine ⟨88923567826181526442984343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237129514203150737181291581 88923567826181526442984343)
    ·
      refine ⟨133385351739272289664476515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88923567826181526442984343 133385351739272289664476515)
      ·
        refine ⟨200078027608908434496714773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133385351739272289664476515 200078027608908434496714773)
        ·
          refine ⟨9378657544167582867033505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200078027608908434496714773 9378657544167582867033505)
          ·
            refine ⟨7033993158125687150275129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378657544167582867033505 7033993158125687150275129)
            ·
              refine ⟨5275494868594265362706347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7033993158125687150275129 5275494868594265362706347)
              ·
                refine ⟨7913242302891398044059521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275494868594265362706347 7913242302891398044059521)
                ·
                  refine ⟨5934931727168548533044641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913242302891398044059521 5934931727168548533044641)
                  ·
                    refine ⟨4451198795376411399783481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5934931727168548533044641 4451198795376411399783481)
                    ·
                      refine ⟨3338399096532308549837611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451198795376411399783481 3338399096532308549837611)
                      ·
                        rfl

theorem cell23_6501509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_6501509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501509 prefixEnd_6501509 := by exact prefixLift 6501509
  have htrace : WordTrace (prefixWord ++ tailWord_6501509) baseStart_6501509 baseEnd_6501509 := by
    simpa [prefixWord, tailWord_6501509, baseEnd_6501509] using wordTrace_append hprefix tailTrace_6501509
  have hstable : (prefixWord ++ tailWord_6501509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501509).length < 2 ^ (prefixWord ++ tailWord_6501509).sum := by decide
  have hdescent : baseEnd_6501509 < baseStart_6501509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501528 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_6501528 : Nat := 118140960795 + 6501528 * 2 ^ 59
def prefixEnd_6501528 : Nat := 4983230072969 + 3 ^ 40 * 6501528 * 2
def baseEnd_6501528 : Nat := 1112802950888247991833341

theorem tailTrace_6501528 : CollatzResearch.WordTrace tailWord_6501528 prefixEnd_6501528 1112802950888247991833341 := by
  unfold tailWord_6501528
  simp only [CollatzResearch.WordTrace]
  refine ⟨118565103595040951713116619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158086804793387935617488825 118565103595040951713116619)
  ·
    refine ⟨177847655392561427569674929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118565103595040951713116619 177847655392561427569674929)
    ·
      refine ⟨133385741544421070677256197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177847655392561427569674929 133385741544421070677256197)
      ·
        refine ⟨25009826539578950751985537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133385741544421070677256197 25009826539578950751985537)
        ·
          refine ⟨18757369904684213063989153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25009826539578950751985537 18757369904684213063989153)
          ·
            refine ⟨14068027428513159797991865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18757369904684213063989153 14068027428513159797991865)
            ·
              refine ⟨10551020571384869848493899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14068027428513159797991865 10551020571384869848493899)
              ·
                refine ⟨15826530857077304772740849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10551020571384869848493899 15826530857077304772740849)
                ·
                  refine ⟨11869898142807978579555637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15826530857077304772740849 11869898142807978579555637)
                  ·
                    refine ⟨1112802950888247991833341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11869898142807978579555637 1112802950888247991833341)
                    ·
                      rfl

theorem cell23_6501528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_6501528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501528 prefixEnd_6501528 := by exact prefixLift 6501528
  have htrace : WordTrace (prefixWord ++ tailWord_6501528) baseStart_6501528 baseEnd_6501528 := by
    simpa [prefixWord, tailWord_6501528, baseEnd_6501528] using wordTrace_append hprefix tailTrace_6501528
  have hstable : (prefixWord ++ tailWord_6501528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501528).length < 2 ^ (prefixWord ++ tailWord_6501528).sum := by decide
  have hdescent : baseEnd_6501528 < baseStart_6501528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501549 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 5]
def baseStart_6501549 : Nat := 118140960795 + 6501549 * 2 ^ 59
def prefixEnd_6501549 : Nat := 4983230072969 + 3 ^ 40 * 6501549 * 2
def baseEnd_6501549 : Nat := 370935515084276488148603

theorem tailTrace_6501549 : CollatzResearch.WordTrace tailWord_6501549 prefixEnd_6501549 370935515084276488148603 := by
  unfold tailWord_6501549
  simp only [CollatzResearch.WordTrace]
  refine ⟨237130973123005824012747701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158087315415337216008498467 237130973123005824012747701)
  ·
    refine ⟨22231028730281796001195097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237130973123005824012747701 22231028730281796001195097)
    ·
      refine ⟨16673271547711347000896323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22231028730281796001195097 16673271547711347000896323)
      ·
        refine ⟨25009907321567020501344485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16673271547711347000896323 25009907321567020501344485)
        ·
          refine ⟨4689357622793816344002091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25009907321567020501344485 4689357622793816344002091)
          ·
            refine ⟨7034036434190724516003137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689357622793816344002091 7034036434190724516003137)
            ·
              refine ⟨5275527325643043387002353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034036434190724516003137 5275527325643043387002353)
              ·
                refine ⟨3956645494232282540251765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275527325643043387002353 3956645494232282540251765)
                ·
                  refine ⟨370935515084276488148603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956645494232282540251765 370935515084276488148603)
                  ·
                    rfl

theorem cell23_6501549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_6501549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501549 prefixEnd_6501549 := by exact prefixLift 6501549
  have htrace : WordTrace (prefixWord ++ tailWord_6501549) baseStart_6501549 baseEnd_6501549 := by
    simpa [prefixWord, tailWord_6501549, baseEnd_6501549] using wordTrace_append hprefix tailTrace_6501549
  have hstable : (prefixWord ++ tailWord_6501549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501549).length < 2 ^ (prefixWord ++ tailWord_6501549).sum := by decide
  have hdescent : baseEnd_6501549 < baseStart_6501549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501582 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_6501582 : Nat := 118140960795 + 6501582 * 2 ^ 59
def prefixEnd_6501582 : Nat := 4983230072969 + 3 ^ 40 * 6501582 * 2
def baseEnd_6501582 : Nat := 3338436580620086764224775

theorem tailTrace_6501582 : CollatzResearch.WordTrace tailWord_6501582 prefixEnd_6501582 3338436580620086764224775 := by
  unfold tailWord_6501582
  simp only [CollatzResearch.WordTrace]
  refine ⟨29641522091485783831087375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158088117821257513765799333 29641522091485783831087375)
  ·
    refine ⟨44462283137228675746631063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29641522091485783831087375 44462283137228675746631063)
    ·
      refine ⟨66693424705843013619946595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44462283137228675746631063 66693424705843013619946595)
      ·
        refine ⟨100040137058764520429919893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66693424705843013619946595 100040137058764520429919893)
        ·
          refine ⟨4689381424629586895152495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100040137058764520429919893 4689381424629586895152495)
          ·
            refine ⟨7034072136944380342728743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689381424629586895152495 7034072136944380342728743)
            ·
              refine ⟨10551108205416570514093115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034072136944380342728743 10551108205416570514093115)
              ·
                refine ⟨15826662308124855771139673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10551108205416570514093115 15826662308124855771139673)
                ·
                  refine ⟨11869996731093641828354755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15826662308124855771139673 11869996731093641828354755)
                  ·
                    refine ⟨17804995096640462742532133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11869996731093641828354755 17804995096640462742532133)
                    ·
                      refine ⟨3338436580620086764224775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17804995096640462742532133 3338436580620086764224775)
                      ·
                        rfl

theorem cell23_6501582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_6501582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501582 prefixEnd_6501582 := by exact prefixLift 6501582
  have htrace : WordTrace (prefixWord ++ tailWord_6501582) baseStart_6501582 baseEnd_6501582 := by
    simpa [prefixWord, tailWord_6501582, baseEnd_6501582] using wordTrace_append hprefix tailTrace_6501582
  have hstable : (prefixWord ++ tailWord_6501582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501582).length < 2 ^ (prefixWord ++ tailWord_6501582).sum := by decide
  have hdescent : baseEnd_6501582 < baseStart_6501582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501592 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 1, 4]
def baseStart_6501592 : Nat := 118140960795 + 6501592 * 2 ^ 59
def prefixEnd_6501592 : Nat := 4983230072969 + 3 ^ 40 * 6501592 * 2
def baseEnd_6501592 : Nat := 1112813905142210575033243

theorem tailTrace_6501592 : CollatzResearch.WordTrace tailWord_6501592 prefixEnd_6501592 1112813905142210575033243 := by
  unfold tailWord_6501592
  simp only [CollatzResearch.WordTrace]
  refine ⟨118566270730925021178281515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158088360974566694904375353 118566270730925021178281515)
  ·
    refine ⟨177849406096387531767422273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118566270730925021178281515 177849406096387531767422273)
    ·
      refine ⟨133387054572290648825566705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177849406096387531767422273 133387054572290648825566705)
      ·
        refine ⟨100040290929217986619175029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133387054572290648825566705 100040290929217986619175029)
        ·
          refine ⟨9378777274614186245547659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100040290929217986619175029 9378777274614186245547659)
          ·
            refine ⟨14068165911921279368321489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378777274614186245547659 14068165911921279368321489)
            ·
              refine ⟨10551124433940959526241117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14068165911921279368321489 10551124433940959526241117)
              ·
                refine ⟨3956671662727859822340419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10551124433940959526241117 3956671662727859822340419)
                ·
                  refine ⟨5935007494091789733510629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956671662727859822340419 5935007494091789733510629)
                  ·
                    refine ⟨1112813905142210575033243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935007494091789733510629 1112813905142210575033243)
                    ·
                      rfl

theorem cell23_6501592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_6501592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501592 prefixEnd_6501592 := by exact prefixLift 6501592
  have htrace : WordTrace (prefixWord ++ tailWord_6501592) baseStart_6501592 baseEnd_6501592 := by
    simpa [prefixWord, tailWord_6501592, baseEnd_6501592] using wordTrace_append hprefix tailTrace_6501592
  have hstable : (prefixWord ++ tailWord_6501592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501592).length < 2 ^ (prefixWord ++ tailWord_6501592).sum := by decide
  have hdescent : baseEnd_6501592 < baseStart_6501592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501605 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 6]
def baseStart_6501605 : Nat := 118140960795 + 6501605 * 2 ^ 59
def prefixEnd_6501605 : Nat := 4983230072969 + 3 ^ 40 * 6501605 * 2
def baseEnd_6501605 : Nat := 370938710075015574915241

theorem tailTrace_6501605 : CollatzResearch.WordTrace tailWord_6501605 prefixEnd_6501605 370938710075015574915241 := by
  unfold tailWord_6501605
  simp only [CollatzResearch.WordTrace]
  refine ⟨237133015610802945576786269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158088677073868630384524179 237133015610802945576786269)
  ·
    refine ⟨88924880854051104591294851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237133015610802945576786269 88924880854051104591294851)
    ·
      refine ⟨133387321281076656886942277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88924880854051104591294851 133387321281076656886942277)
      ·
        refine ⟨25010122740201873166301677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133387321281076656886942277 25010122740201873166301677)
        ·
          refine ⟨9378796027575702437363129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25010122740201873166301677 9378796027575702437363129)
          ·
            refine ⟨7034097020681776828022347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378796027575702437363129 7034097020681776828022347)
            ·
              refine ⟨10551145531022665242033521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034097020681776828022347 10551145531022665242033521)
              ·
                refine ⟨7913359148266998931525141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551145531022665242033521 7913359148266998931525141)
                ·
                  refine ⟨370938710075015574915241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7913359148266998931525141 370938710075015574915241)
                  ·
                    rfl

theorem cell23_6501605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_6501605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501605 prefixEnd_6501605 := by exact prefixLift 6501605
  have htrace : WordTrace (prefixWord ++ tailWord_6501605) baseStart_6501605 baseEnd_6501605 := by
    simpa [prefixWord, tailWord_6501605, baseEnd_6501605] using wordTrace_append hprefix tailTrace_6501605
  have hstable : (prefixWord ++ tailWord_6501605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501605).length < 2 ^ (prefixWord ++ tailWord_6501605).sum := by decide
  have hdescent : baseEnd_6501605 < baseStart_6501605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501641 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_6501641 : Nat := 118140960795 + 6501641 * 2 ^ 59
def prefixEnd_6501641 : Nat := 4983230072969 + 3 ^ 40 * 6501641 * 2
def baseEnd_6501641 : Nat := 3338466875978702033387003

theorem tailTrace_6501641 : CollatzResearch.WordTrace tailWord_6501641 prefixEnd_6501641 3338466875978702033387003 := by
  unfold tailWord_6501641
  simp only [CollatzResearch.WordTrace]
  refine ⟨237134328638672523725096777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158089552425781682483397851 237134328638672523725096777)
  ·
    refine ⟨177850746479004392793822583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237134328638672523725096777 177850746479004392793822583)
    ·
      refine ⟨266776119718506589190733875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177850746479004392793822583 266776119718506589190733875)
      ·
        refine ⟨400164179577759883786100813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266776119718506589190733875 400164179577759883786100813)
        ·
          refine ⟨150061567341659956419787805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400164179577759883786100813 150061567341659956419787805)
          ·
            refine ⟨56273087753122483657420427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150061567341659956419787805 56273087753122483657420427)
            ·
              refine ⟨84409631629683725486130641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56273087753122483657420427 84409631629683725486130641)
              ·
                refine ⟨63307223722262794114597981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84409631629683725486130641 63307223722262794114597981)
                ·
                  refine ⟨23740208895848547792974243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63307223722262794114597981 23740208895848547792974243)
                  ·
                    refine ⟨35610313343772821689461365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23740208895848547792974243 35610313343772821689461365)
                    ·
                      refine ⟨3338466875978702033387003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35610313343772821689461365 3338466875978702033387003)
                      ·
                        rfl

theorem cell23_6501641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_6501641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501641 prefixEnd_6501641 := by exact prefixLift 6501641
  have htrace : WordTrace (prefixWord ++ tailWord_6501641) baseStart_6501641 baseEnd_6501641 := by
    simpa [prefixWord, tailWord_6501641, baseEnd_6501641] using wordTrace_append hprefix tailTrace_6501641
  have hstable : (prefixWord ++ tailWord_6501641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501641).length < 2 ^ (prefixWord ++ tailWord_6501641).sum := by decide
  have hdescent : baseEnd_6501641 < baseStart_6501641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501658 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_6501658 : Nat := 118140960795 + 6501658 * 2 ^ 59
def prefixEnd_6501658 : Nat := 4983230072969 + 3 ^ 40 * 6501658 * 2
def baseEnd_6501658 : Nat := 3338475605149828466874425

theorem tailTrace_6501658 : CollatzResearch.WordTrace tailWord_6501658 prefixEnd_6501658 3338475605149828466874425 := by
  unfold tailWord_6501658
  simp only [CollatzResearch.WordTrace]
  refine ⟨59283737169902733907116407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158089965786407290418977085 59283737169902733907116407)
  ·
    refine ⟨88925605754854100860674611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59283737169902733907116407 88925605754854100860674611)
    ·
      refine ⟨133388408632281151291011917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88925605754854100860674611 133388408632281151291011917)
      ·
        refine ⟨50020653237105431734129469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133388408632281151291011917 50020653237105431734129469)
        ·
          refine ⟨18757744963914536900298551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50020653237105431734129469 18757744963914536900298551)
          ·
            refine ⟨28136617445871805350447827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18757744963914536900298551 28136617445871805350447827)
            ·
              refine ⟨42204926168807708025671741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28136617445871805350447827 42204926168807708025671741)
              ·
                refine ⟨15826847313302890509626903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42204926168807708025671741 15826847313302890509626903)
                ·
                  refine ⟨23740270969954335764440355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15826847313302890509626903 23740270969954335764440355)
                  ·
                    refine ⟨35610406454931503646660533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23740270969954335764440355 35610406454931503646660533)
                    ·
                      refine ⟨3338475605149828466874425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35610406454931503646660533 3338475605149828466874425)
                      ·
                        rfl

theorem cell23_6501658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_6501658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501658 prefixEnd_6501658 := by exact prefixLift 6501658
  have htrace : WordTrace (prefixWord ++ tailWord_6501658) baseStart_6501658 baseEnd_6501658 := by
    simpa [prefixWord, tailWord_6501658, baseEnd_6501658] using wordTrace_append hprefix tailTrace_6501658
  have hstable : (prefixWord ++ tailWord_6501658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501658).length < 2 ^ (prefixWord ++ tailWord_6501658).sum := by decide
  have hdescent : baseEnd_6501658 < baseStart_6501658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501666 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_6501666 : Nat := 118140960795 + 6501666 * 2 ^ 59
def prefixEnd_6501666 : Nat := 4983230072969 + 3 ^ 40 * 6501666 * 2
def baseEnd_6501666 : Nat := 3338479712995064435574389

theorem tailTrace_6501666 : CollatzResearch.WordTrace tailWord_6501666 prefixEnd_6501666 3338479712995064435574389 := by
  unfold tailWord_6501666
  simp only [CollatzResearch.WordTrace]
  refine ⟨59283810115895488248689213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158090160309054635329837901 59283810115895488248689213)
  ·
    refine ⟨22231428793460808093258455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59283810115895488248689213 22231428793460808093258455)
    ·
      refine ⟨33347143190191212139887683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22231428793460808093258455 33347143190191212139887683)
      ·
        refine ⟨50020714785286818209831525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33347143190191212139887683 50020714785286818209831525)
        ·
          refine ⟨9378884022241278414343411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50020714785286818209831525 9378884022241278414343411)
          ·
            refine ⟨14068326033361917621515117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378884022241278414343411 14068326033361917621515117)
            ·
              refine ⟨5275622262510719108068169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14068326033361917621515117 5275622262510719108068169)
              ·
                refine ⟨3956716696883039331051127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275622262510719108068169 3956716696883039331051127)
                ·
                  refine ⟨5935075045324558996576691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956716696883039331051127 5935075045324558996576691)
                  ·
                    refine ⟨8902612567986838494865037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935075045324558996576691 8902612567986838494865037)
                    ·
                      refine ⟨3338479712995064435574389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8902612567986838494865037 3338479712995064435574389)
                      ·
                        rfl

theorem cell23_6501666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_6501666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501666 prefixEnd_6501666 := by exact prefixLift 6501666
  have htrace : WordTrace (prefixWord ++ tailWord_6501666) baseStart_6501666 baseEnd_6501666 := by
    simpa [prefixWord, tailWord_6501666, baseEnd_6501666] using wordTrace_append hprefix tailTrace_6501666
  have hstable : (prefixWord ++ tailWord_6501666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501666).length < 2 ^ (prefixWord ++ tailWord_6501666).sum := by decide
  have hdescent : baseEnd_6501666 < baseStart_6501666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501682 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_6501682 : Nat := 118140960795 + 6501682 * 2 ^ 59
def prefixEnd_6501682 : Nat := 4983230072969 + 3 ^ 40 * 6501682 * 2
def baseEnd_6501682 : Nat := 1112829309561845457658105

theorem tailTrace_6501682 : CollatzResearch.WordTrace tailWord_6501682 prefixEnd_6501682 1112829309561845457658105 := by
  unfold tailWord_6501682
  simp only [CollatzResearch.WordTrace]
  refine ⟨59283956007880996931834825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158090549354349325151559533 59283956007880996931834825)
  ·
    refine ⟨44462967005910747698876119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59283956007880996931834825 44462967005910747698876119)
    ·
      refine ⟨66694450508866121548314179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44462967005910747698876119 66694450508866121548314179)
      ·
        refine ⟨100041675763299182322471269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66694450508866121548314179 100041675763299182322471269)
        ·
          refine ⟨18757814205618596685463363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100041675763299182322471269 18757814205618596685463363)
          ·
            refine ⟨28136721308427895028195045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18757814205618596685463363 28136721308427895028195045)
            ·
              refine ⟨5275635245330230317786571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28136721308427895028195045 5275635245330230317786571)
              ·
                refine ⟨7913452867995345476679857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275635245330230317786571 7913452867995345476679857)
                ·
                  refine ⟨5935089650996509107509893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913452867995345476679857 5935089650996509107509893)
                  ·
                    refine ⟨1112829309561845457658105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935089650996509107509893 1112829309561845457658105)
                    ·
                      rfl

theorem cell23_6501682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_6501682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501682 prefixEnd_6501682 := by exact prefixLift 6501682
  have htrace : WordTrace (prefixWord ++ tailWord_6501682) baseStart_6501682 baseEnd_6501682 := by
    simpa [prefixWord, tailWord_6501682, baseEnd_6501682] using wordTrace_append hprefix tailTrace_6501682
  have hstable : (prefixWord ++ tailWord_6501682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501682).length < 2 ^ (prefixWord ++ tailWord_6501682).sum := by decide
  have hdescent : baseEnd_6501682 < baseStart_6501682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501686 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6501686 : Nat := 118140960795 + 6501686 * 2 ^ 59
def prefixEnd_6501686 : Nat := 4983230072969 + 3 ^ 40 * 6501686 * 2
def baseEnd_6501686 : Nat := 1112829994202718119108099

theorem tailTrace_6501686 : CollatzResearch.WordTrace tailWord_6501686 prefixEnd_6501686 1112829994202718119108099 := by
  unfold tailWord_6501686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820998120219343525655307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158090646615672997606989941 14820998120219343525655307)
  ·
    refine ⟨22231497180329015288482961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14820998120219343525655307 22231497180329015288482961)
    ·
      refine ⟨16673622885246761466362221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22231497180329015288482961 16673622885246761466362221)
      ·
        refine ⟨6252608581967535549885833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16673622885246761466362221 6252608581967535549885833)
        ·
          refine ⟨4689456436475651662414375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6252608581967535549885833 4689456436475651662414375)
          ·
            refine ⟨7034184654713477493621563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689456436475651662414375 7034184654713477493621563)
            ·
              refine ⟨10551276982070216240432345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034184654713477493621563 10551276982070216240432345)
              ·
                refine ⟨7913457736552662180324259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551276982070216240432345 7913457736552662180324259)
                ·
                  refine ⟨11870186604828993270486389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7913457736552662180324259 11870186604828993270486389)
                  ·
                    refine ⟨1112829994202718119108099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11870186604828993270486389 1112829994202718119108099)
                    ·
                      rfl

theorem cell23_6501686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6501686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501686 prefixEnd_6501686 := by exact prefixLift 6501686
  have htrace : WordTrace (prefixWord ++ tailWord_6501686) baseStart_6501686 baseEnd_6501686 := by
    simpa [prefixWord, tailWord_6501686, baseEnd_6501686] using wordTrace_append hprefix tailTrace_6501686
  have hstable : (prefixWord ++ tailWord_6501686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501686).length < 2 ^ (prefixWord ++ tailWord_6501686).sum := by decide
  have hdescent : baseEnd_6501686 < baseStart_6501686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501688 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_6501688 : Nat := 118140960795 + 6501688 * 2 ^ 59
def prefixEnd_6501688 : Nat := 4983230072969 + 3 ^ 40 * 6501688 * 2
def baseEnd_6501688 : Nat := 3338491009569463349499287

theorem tailTrace_6501688 : CollatzResearch.WordTrace tailWord_6501688 prefixEnd_6501688 3338491009569463349499287 := by
  unfold tailWord_6501688
  simp only [CollatzResearch.WordTrace]
  refine ⟨118568021434751125376028859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158090695246334833834705145 118568021434751125376028859)
  ·
    refine ⟨177852032152126688064043289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118568021434751125376028859 177852032152126688064043289)
    ·
      refine ⟨133389024114095016048032467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177852032152126688064043289 133389024114095016048032467)
      ·
        refine ⟨200083536171142524072048701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133389024114095016048032467 200083536171142524072048701)
        ·
          refine ⟨75031326064178446527018263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200083536171142524072048701 75031326064178446527018263)
          ·
            refine ⟨112546989096267669790527395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75031326064178446527018263 112546989096267669790527395)
            ·
              refine ⟨168820483644401504685791093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112546989096267669790527395 168820483644401504685791093)
              ·
                refine ⟨15826920341662641064292915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168820483644401504685791093 15826920341662641064292915)
                ·
                  refine ⟨23740380512493961596439373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15826920341662641064292915 23740380512493961596439373)
                  ·
                    refine ⟨8902642692185235598664765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23740380512493961596439373 8902642692185235598664765)
                    ·
                      refine ⟨3338491009569463349499287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8902642692185235598664765 3338491009569463349499287)
                      ·
                        rfl

theorem cell23_6501688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_6501688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501688 prefixEnd_6501688 := by exact prefixLift 6501688
  have htrace : WordTrace (prefixWord ++ tailWord_6501688) baseStart_6501688 baseEnd_6501688 := by
    simpa [prefixWord, tailWord_6501688, baseEnd_6501688] using wordTrace_append hprefix tailTrace_6501688
  have hstable : (prefixWord ++ tailWord_6501688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501688).length < 2 ^ (prefixWord ++ tailWord_6501688).sum := by decide
  have hdescent : baseEnd_6501688 < baseStart_6501688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501689 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6501689 : Nat := 118140960795 + 6501689 * 2 ^ 59
def prefixEnd_6501689 : Nat := 4983230072969 + 3 ^ 40 * 6501689 * 2
def baseEnd_6501689 : Nat := 3338491523050117845586783

theorem tailTrace_6501689 : CollatzResearch.WordTrace tailWord_6501689 prefixEnd_6501689 3338491523050117845586783 := by
  unfold tailWord_6501689
  simp only [CollatzResearch.WordTrace]
  refine ⟨237136079342498627922844121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158090719561665751948562747 237136079342498627922844121)
  ·
    refine ⟨177852059506873970942133091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237136079342498627922844121 177852059506873970942133091)
    ·
      refine ⟨266778089260310956413199637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177852059506873970942133091 266778089260310956413199637)
      ·
        refine ⟨12505222934077076081868733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266778089260310956413199637 12505222934077076081868733)
        ·
          refine ⟨4689458600278903530700775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12505222934077076081868733 4689458600278903530700775)
          ·
            refine ⟨7034187900418355296051163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689458600278903530700775 7034187900418355296051163)
            ·
              refine ⟨10551281850627532944076745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034187900418355296051163 10551281850627532944076745)
              ·
                refine ⟨7913461387970649708057559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551281850627532944076745 7913461387970649708057559)
                ·
                  refine ⟨11870192081955974562086339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7913461387970649708057559 11870192081955974562086339)
                  ·
                    refine ⟨17805288122933961843129509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11870192081955974562086339 17805288122933961843129509)
                    ·
                      refine ⟨3338491523050117845586783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17805288122933961843129509 3338491523050117845586783)
                      ·
                        rfl

theorem cell23_6501689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6501689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501689 prefixEnd_6501689 := by exact prefixLift 6501689
  have htrace : WordTrace (prefixWord ++ tailWord_6501689) baseStart_6501689 baseEnd_6501689 := by
    simpa [prefixWord, tailWord_6501689, baseEnd_6501689] using wordTrace_append hprefix tailTrace_6501689
  have hstable : (prefixWord ++ tailWord_6501689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501689).length < 2 ^ (prefixWord ++ tailWord_6501689).sum := by decide
  have hdescent : baseEnd_6501689 < baseStart_6501689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501692 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_6501692 : Nat := 118140960795 + 6501692 * 2 ^ 59
def prefixEnd_6501692 : Nat := 4983230072969 + 3 ^ 40 * 6501692 * 2
def baseEnd_6501692 : Nat := 3338493063492081333849269

theorem tailTrace_6501692 : CollatzResearch.WordTrace tailWord_6501692 prefixEnd_6501692 3338493063492081333849269 := by
  unfold tailWord_6501692
  simp only [CollatzResearch.WordTrace]
  refine ⟨118568094380743879717601665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158090792507658506290135553 118568094380743879717601665)
  ·
    refine ⟨88926070785557909788201249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118568094380743879717601665 88926070785557909788201249)
    ·
      refine ⟨66694553089168432341150937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88926070785557909788201249 66694553089168432341150937)
      ·
        refine ⟨50020914816876324255863203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66694553089168432341150937 50020914816876324255863203)
        ·
          refine ⟨75031372225314486383794805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50020914816876324255863203 75031372225314486383794805)
          ·
            refine ⟨7034191146123233098480763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75031372225314486383794805 7034191146123233098480763)
            ·
              refine ⟨10551286719184849647721145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034191146123233098480763 10551286719184849647721145)
              ·
                refine ⟨7913465039388637235790859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551286719184849647721145 7913465039388637235790859)
                ·
                  refine ⟨11870197559082955853686289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7913465039388637235790859 11870197559082955853686289)
                  ·
                    refine ⟨8902648169312216890264717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11870197559082955853686289 8902648169312216890264717)
                    ·
                      refine ⟨3338493063492081333849269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8902648169312216890264717 3338493063492081333849269)
                      ·
                        rfl

theorem cell23_6501692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_6501692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501692 prefixEnd_6501692 := by exact prefixLift 6501692
  have htrace : WordTrace (prefixWord ++ tailWord_6501692) baseStart_6501692 baseEnd_6501692 := by
    simpa [prefixWord, tailWord_6501692, baseEnd_6501692] using wordTrace_append hprefix tailTrace_6501692
  have hstable : (prefixWord ++ tailWord_6501692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501692).length < 2 ^ (prefixWord ++ tailWord_6501692).sum := by decide
  have hdescent : baseEnd_6501692 < baseStart_6501692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501701 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_6501701 : Nat := 118140960795 + 6501701 * 2 ^ 59
def prefixEnd_6501701 : Nat := 4983230072969 + 3 ^ 40 * 6501701 * 2
def baseEnd_6501701 : Nat := 3338497684817971798636727

theorem tailTrace_6501701 : CollatzResearch.WordTrace tailWord_6501701 prefixEnd_6501701 3338497684817971798636727 := by
  unfold tailWord_6501701
  simp only [CollatzResearch.WordTrace]
  refine ⟨237136517018455153972280957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158091011345636769314853971 237136517018455153972280957)
  ·
    refine ⟨88926193881920682739605359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237136517018455153972280957 88926193881920682739605359)
    ·
      refine ⟨133389290822881024109408039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88926193881920682739605359 133389290822881024109408039)
      ·
        refine ⟨200083936234321536164112059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133389290822881024109408039 200083936234321536164112059)
        ·
          refine ⟨300125904351482304246168089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200083936234321536164112059 300125904351482304246168089)
          ·
            refine ⟨225094428263611728184626067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300125904351482304246168089 225094428263611728184626067)
            ·
              refine ⟨337641642395417592276939101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225094428263611728184626067 337641642395417592276939101)
              ·
                refine ⟨126615615898281597103852163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337641642395417592276939101 126615615898281597103852163)
                ·
                  refine ⟨189923423847422395655778245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126615615898281597103852163 189923423847422395655778245)
                  ·
                    refine ⟨35610641971391699185458421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189923423847422395655778245 35610641971391699185458421)
                    ·
                      refine ⟨3338497684817971798636727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35610641971391699185458421 3338497684817971798636727)
                      ·
                        rfl

theorem cell23_6501701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_6501701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501701 prefixEnd_6501701 := by exact prefixLift 6501701
  have htrace : WordTrace (prefixWord ++ tailWord_6501701) baseStart_6501701 baseEnd_6501701 := by
    simpa [prefixWord, tailWord_6501701, baseEnd_6501701] using wordTrace_append hprefix tailTrace_6501701
  have hstable : (prefixWord ++ tailWord_6501701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501701).length < 2 ^ (prefixWord ++ tailWord_6501701).sum := by decide
  have hdescent : baseEnd_6501701 < baseStart_6501701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501709 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_6501709 : Nat := 118140960795 + 6501709 * 2 ^ 59
def prefixEnd_6501709 : Nat := 4983230072969 + 3 ^ 40 * 6501709 * 2
def baseEnd_6501709 : Nat := 3338501792663207767336691

theorem tailTrace_6501709 : CollatzResearch.WordTrace tailWord_6501709 prefixEnd_6501709 3338501792663207767336691 := by
  unfold tailWord_6501709
  simp only [CollatzResearch.WordTrace]
  refine ⟨237136808802426171338572181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158091205868284114225714787 237136808802426171338572181)
  ·
    refine ⟨11115787912613726781495571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237136808802426171338572181 11115787912613726781495571)
    ·
      refine ⟨16673681868920590172243357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11115787912613726781495571 16673681868920590172243357)
      ·
        refine ⟨6252630700845221314591259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16673681868920590172243357 6252630700845221314591259)
        ·
          refine ⟨9378946051267831971886889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252630700845221314591259 9378946051267831971886889)
          ·
            refine ⟨7034209538450873978915167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378946051267831971886889 7034209538450873978915167)
            ·
              refine ⟨10551314307676310968372751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034209538450873978915167 10551314307676310968372751)
              ·
                refine ⟨15826971461514466452559127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10551314307676310968372751 15826971461514466452559127)
                ·
                  refine ⟨23740457192271699678838691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15826971461514466452559127 23740457192271699678838691)
                  ·
                    refine ⟨35610685788407549518258037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23740457192271699678838691 35610685788407549518258037)
                    ·
                      refine ⟨3338501792663207767336691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35610685788407549518258037 3338501792663207767336691)
                      ·
                        rfl

theorem cell23_6501709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_6501709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501709 prefixEnd_6501709 := by exact prefixLift 6501709
  have htrace : WordTrace (prefixWord ++ tailWord_6501709) baseStart_6501709 baseEnd_6501709 := by
    simpa [prefixWord, tailWord_6501709, baseEnd_6501709] using wordTrace_append hprefix tailTrace_6501709
  have hstable : (prefixWord ++ tailWord_6501709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501709).length < 2 ^ (prefixWord ++ tailWord_6501709).sum := by decide
  have hdescent : baseEnd_6501709 < baseStart_6501709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501728 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_6501728 : Nat := 118140960795 + 6501728 * 2 ^ 59
def prefixEnd_6501728 : Nat := 4983230072969 + 3 ^ 40 * 6501728 * 2
def baseEnd_6501728 : Nat := 3338511548795643192999103

theorem tailTrace_6501728 : CollatzResearch.WordTrace tailWord_6501728 prefixEnd_6501728 3338511548795643192999103 := by
  unfold tailWord_6501728
  simp only [CollatzResearch.WordTrace]
  refine ⟨118568750894678668791756919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158091667859571558389009225 118568750894678668791756919)
  ·
    refine ⟨177853126342018003187635379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118568750894678668791756919 177853126342018003187635379)
    ·
      refine ⟨266779689513027004781453069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177853126342018003187635379 266779689513027004781453069)
      ·
        refine ⟨100042383567385126793044901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266779689513027004781453069 100042383567385126793044901)
        ·
          refine ⟨18757946918884711273695919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100042383567385126793044901 18757946918884711273695919)
          ·
            refine ⟨28136920378327066910543879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18757946918884711273695919 28136920378327066910543879)
            ·
              refine ⟨42205380567490600365815819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28136920378327066910543879 42205380567490600365815819)
              ·
                refine ⟨63308070851235900548723729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42205380567490600365815819 63308070851235900548723729)
                ·
                  refine ⟨47481053138426925411542797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63308070851235900548723729 47481053138426925411542797)
                  ·
                    refine ⟨17805394926910097029328549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47481053138426925411542797 17805394926910097029328549)
                    ·
                      refine ⟨3338511548795643192999103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17805394926910097029328549 3338511548795643192999103)
                      ·
                        rfl

theorem cell23_6501728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_6501728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501728 prefixEnd_6501728 := by exact prefixLift 6501728
  have htrace : WordTrace (prefixWord ++ tailWord_6501728) baseStart_6501728 baseEnd_6501728 := by
    simpa [prefixWord, tailWord_6501728, baseEnd_6501728] using wordTrace_append hprefix tailTrace_6501728
  have hstable : (prefixWord ++ tailWord_6501728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501728).length < 2 ^ (prefixWord ++ tailWord_6501728).sum := by decide
  have hdescent : baseEnd_6501728 < baseStart_6501728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501745 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_6501745 : Nat := 118140960795 + 6501745 * 2 ^ 59
def prefixEnd_6501745 : Nat := 4983230072969 + 3 ^ 40 * 6501745 * 2
def baseEnd_6501745 : Nat := 3338520277966769626486525

theorem tailTrace_6501745 : CollatzResearch.WordTrace tailWord_6501745 prefixEnd_6501745 3338520277966769626486525 := by
  unfold tailWord_6501745
  simp only [CollatzResearch.WordTrace]
  refine ⟨237138121830295749486882689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158092081220197166324588459 237138121830295749486882689)
  ·
    refine ⟨177853591372721812115162017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237138121830295749486882689 177853591372721812115162017)
    ·
      refine ⟨133390193529541359086371513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177853591372721812115162017 133390193529541359086371513)
      ·
        refine ⟨100042645147156019314778635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133390193529541359086371513 100042645147156019314778635)
        ·
          refine ⟨150063967720734028972167953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100042645147156019314778635 150063967720734028972167953)
          ·
            refine ⟨112547975790550521729125965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150063967720734028972167953 112547975790550521729125965)
            ·
              refine ⟨42205490921456445648422237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112547975790550521729125965 42205490921456445648422237)
              ·
                refine ⟨15827059095546167118158339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42205490921456445648422237 15827059095546167118158339)
                ·
                  refine ⟨23740588643319250677237509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15827059095546167118158339 23740588643319250677237509)
                  ·
                    refine ⟨4451360370622359501982033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23740588643319250677237509 4451360370622359501982033)
                    ·
                      refine ⟨3338520277966769626486525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451360370622359501982033 3338520277966769626486525)
                      ·
                        rfl

theorem cell23_6501745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_6501745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501745 prefixEnd_6501745 := by exact prefixLift 6501745
  have htrace : WordTrace (prefixWord ++ tailWord_6501745) baseStart_6501745 baseEnd_6501745 := by
    simpa [prefixWord, tailWord_6501745, baseEnd_6501745] using wordTrace_append hprefix tailTrace_6501745
  have hstable : (prefixWord ++ tailWord_6501745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501745).length < 2 ^ (prefixWord ++ tailWord_6501745).sum := by decide
  have hdescent : baseEnd_6501745 < baseStart_6501745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501785 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 5]
def baseStart_6501785 : Nat := 118140960795 + 6501785 * 2 ^ 59
def prefixEnd_6501785 : Nat := 4983230072969 + 3 ^ 40 * 6501785 * 2
def baseEnd_6501785 : Nat := 370948979688105496665149

theorem tailTrace_6501785 : CollatzResearch.WordTrace tailWord_6501785 prefixEnd_6501785 370948979688105496665149 := by
  unfold tailWord_6501785
  simp only [CollatzResearch.WordTrace]
  refine ⟨237139580750150836318338809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158093053833433890878892539 237139580750150836318338809)
  ·
    refine ⟨177854685562613127238754107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237139580750150836318338809 177854685562613127238754107)
    ·
      refine ⟨266782028343919690858131161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177854685562613127238754107 266782028343919690858131161)
      ·
        refine ⟨200086521257939768143598371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266782028343919690858131161 200086521257939768143598371)
        ·
          refine ⟨300129781886909652215397557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200086521257939768143598371 300129781886909652215397557)
          ·
            refine ⟨28137167051897779895193521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300129781886909652215397557 28137167051897779895193521)
            ·
              refine ⟨21102875288923334921395141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28137167051897779895193521 21102875288923334921395141)
              ·
                refine ⟨3956789116673125297761589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21102875288923334921395141 3956789116673125297761589)
                ·
                  refine ⟨370948979688105496665149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956789116673125297761589 370948979688105496665149)
                  ·
                    rfl

theorem cell23_6501785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 5].length) (baseStart_6501785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501785 prefixEnd_6501785 := by exact prefixLift 6501785
  have htrace : WordTrace (prefixWord ++ tailWord_6501785) baseStart_6501785 baseEnd_6501785 := by
    simpa [prefixWord, tailWord_6501785, baseEnd_6501785] using wordTrace_append hprefix tailTrace_6501785
  have hstable : (prefixWord ++ tailWord_6501785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501785).length < 2 ^ (prefixWord ++ tailWord_6501785).sum := by decide
  have hdescent : baseEnd_6501785 < baseStart_6501785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501835 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 4, 4, 2]
def baseStart_6501835 : Nat := 118140960795 + 6501835 * 2 ^ 59
def prefixEnd_6501835 : Nat := 4983230072969 + 3 ^ 40 * 6501835 * 2
def baseEnd_6501835 : Nat := 3338566491225674274361111

theorem tailTrace_6501835 : CollatzResearch.WordTrace tailWord_6501835 prefixEnd_6501835 3338566491225674274361111 := by
  unfold tailWord_6501835
  simp only [CollatzResearch.WordTrace]
  refine ⟨237141404399969694857658959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158094269599979796571772639 237141404399969694857658959)
  ·
    refine ⟨355712106599954542286488439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237141404399969694857658959 355712106599954542286488439)
    ·
      refine ⟨533568159899931813429732659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355712106599954542286488439 533568159899931813429732659)
      ·
        refine ⟨800352239849897720144598989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533568159899931813429732659 800352239849897720144598989)
        ·
          refine ⟨300132089943711645054224621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800352239849897720144598989 300132089943711645054224621)
          ·
            refine ⟨112549533728891866895334233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300132089943711645054224621 112549533728891866895334233)
            ·
              refine ⟨84412150296668900171500675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112549533728891866895334233 84412150296668900171500675)
              ·
                refine ⟨126618225445003350257251013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84412150296668900171500675 126618225445003350257251013)
                ·
                  refine ⟨23740917270938128173234565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126618225445003350257251013 23740917270938128173234565)
                  ·
                    refine ⟨4451421988300899032481481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23740917270938128173234565 4451421988300899032481481)
                    ·
                      refine ⟨3338566491225674274361111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451421988300899032481481 3338566491225674274361111)
                      ·
                        rfl

theorem cell23_6501835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4, 2].length) (baseStart_6501835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501835 prefixEnd_6501835 := by exact prefixLift 6501835
  have htrace : WordTrace (prefixWord ++ tailWord_6501835) baseStart_6501835 baseEnd_6501835 := by
    simpa [prefixWord, tailWord_6501835, baseEnd_6501835] using wordTrace_append hprefix tailTrace_6501835
  have hstable : (prefixWord ++ tailWord_6501835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501835).length < 2 ^ (prefixWord ++ tailWord_6501835).sum := by decide
  have hdescent : baseEnd_6501835 < baseStart_6501835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501848 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6501848 : Nat := 118140960795 + 6501848 * 2 ^ 59
def prefixEnd_6501848 : Nat := 4983230072969 + 3 ^ 40 * 6501848 * 2
def baseEnd_6501848 : Nat := 3338573166474182723498551

theorem tailTrace_6501848 : CollatzResearch.WordTrace tailWord_6501848 prefixEnd_6501848 3338573166474182723498551 := by
  unfold tailWord_6501848
  simp only [CollatzResearch.WordTrace]
  refine ⟨118570939274461299038941099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158094585699281732051921465 118570939274461299038941099)
  ·
    refine ⟨177856408911691948558411649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118570939274461299038941099 177856408911691948558411649)
    ·
      refine ⟨133392306683768961418808737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177856408911691948558411649 133392306683768961418808737)
      ·
        refine ⟨100044230012826721064106553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133392306683768961418808737 100044230012826721064106553)
        ·
          refine ⟨75033172509620040798079915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100044230012826721064106553 75033172509620040798079915)
          ·
            refine ⟨112549758764430061197119873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75033172509620040798079915 112549758764430061197119873)
            ·
              refine ⟨84412319073322545897839905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112549758764430061197119873 84412319073322545897839905)
              ·
                refine ⟨63309239304991909423379929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84412319073322545897839905 63309239304991909423379929)
                ·
                  refine ⟨47481929478743932067534947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63309239304991909423379929 47481929478743932067534947)
                  ·
                    refine ⟨71222894218115898101302421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47481929478743932067534947 71222894218115898101302421)
                    ·
                      refine ⟨3338573166474182723498551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71222894218115898101302421 3338573166474182723498551)
                      ·
                        rfl

theorem cell23_6501848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6501848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501848 prefixEnd_6501848 := by exact prefixLift 6501848
  have htrace : WordTrace (prefixWord ++ tailWord_6501848) baseStart_6501848 baseEnd_6501848 := by
    simpa [prefixWord, tailWord_6501848, baseEnd_6501848] using wordTrace_append hprefix tailTrace_6501848
  have hstable : (prefixWord ++ tailWord_6501848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501848).length < 2 ^ (prefixWord ++ tailWord_6501848).sum := by decide
  have hdescent : baseEnd_6501848 < baseStart_6501848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501855 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_6501855 : Nat := 118140960795 + 6501855 * 2 ^ 59
def prefixEnd_6501855 : Nat := 4983230072969 + 3 ^ 40 * 6501855 * 2
def baseEnd_6501855 : Nat := 3338576760838764196111019

theorem tailTrace_6501855 : CollatzResearch.WordTrace tailWord_6501855 prefixEnd_6501855 3338576760838764196111019 := by
  unfold tailWord_6501855
  simp only [CollatzResearch.WordTrace]
  refine ⟨237142133859897238273387019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158094755906598158848924679 237142133859897238273387019)
  ·
    refine ⟨355713200789845857410080529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237142133859897238273387019 355713200789845857410080529)
    ·
      refine ⟨266784900592384393057560397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355713200789845857410080529 266784900592384393057560397)
      ·
        refine ⟨100044337722144147396585149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266784900592384393057560397 100044337722144147396585149)
        ·
          refine ⟨37516626645804055273719431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100044337722144147396585149 37516626645804055273719431)
          ·
            refine ⟨56274939968706082910579147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37516626645804055273719431 56274939968706082910579147)
            ·
              refine ⟨84412409953059124365868721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56274939968706082910579147 84412409953059124365868721)
              ·
                refine ⟨63309307464794343274401541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84412409953059124365868721 63309307464794343274401541)
                ·
                  refine ⟨11870495149648939363950289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63309307464794343274401541 11870495149648939363950289)
                  ·
                    refine ⟨8902871362236704522962717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11870495149648939363950289 8902871362236704522962717)
                    ·
                      refine ⟨3338576760838764196111019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8902871362236704522962717 3338576760838764196111019)
                      ·
                        rfl

theorem cell23_6501855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_6501855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501855 prefixEnd_6501855 := by exact prefixLift 6501855
  have htrace : WordTrace (prefixWord ++ tailWord_6501855) baseStart_6501855 baseEnd_6501855 := by
    simpa [prefixWord, tailWord_6501855, baseEnd_6501855] using wordTrace_append hprefix tailTrace_6501855
  have hstable : (prefixWord ++ tailWord_6501855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501855).length < 2 ^ (prefixWord ++ tailWord_6501855).sum := by decide
  have hdescent : baseEnd_6501855 < baseStart_6501855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501869 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6501869 : Nat := 118140960795 + 6501869 * 2 ^ 59
def prefixEnd_6501869 : Nat := 4983230072969 + 3 ^ 40 * 6501869 * 2
def baseEnd_6501869 : Nat := 3338583949567927141335955

theorem tailTrace_6501869 : CollatzResearch.WordTrace tailWord_6501869 prefixEnd_6501869 3338583949567927141335955 := by
  unfold tailWord_6501869
  simp only [CollatzResearch.WordTrace]
  refine ⟨237142644481846518664396661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158095096321231012442931107 237142644481846518664396661)
  ·
    refine ⟨22232122920173111124787187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237142644481846518664396661 22232122920173111124787187)
    ·
      refine ⟨33348184380259666687180781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22232122920173111124787187 33348184380259666687180781)
      ·
        refine ⟨12505569142597375007692793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33348184380259666687180781 12505569142597375007692793)
        ·
          refine ⟨9379176856948031255769595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12505569142597375007692793 9379176856948031255769595)
          ·
            refine ⟨14068765285422046883654393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9379176856948031255769595 14068765285422046883654393)
            ·
              refine ⟨10551573964066535162740795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14068765285422046883654393 10551573964066535162740795)
              ·
                refine ⟨15827360946099802744111193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10551573964066535162740795 15827360946099802744111193)
                ·
                  refine ⟨11870520709574852058083395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15827360946099802744111193 11870520709574852058083395)
                  ·
                    refine ⟨17805781064362278087125093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11870520709574852058083395 17805781064362278087125093)
                    ·
                      refine ⟨3338583949567927141335955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17805781064362278087125093 3338583949567927141335955)
                      ·
                        rfl

theorem cell23_6501869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6501869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501869 prefixEnd_6501869 := by exact prefixLift 6501869
  have htrace : WordTrace (prefixWord ++ tailWord_6501869) baseStart_6501869 baseEnd_6501869 := by
    simpa [prefixWord, tailWord_6501869, baseEnd_6501869] using wordTrace_append hprefix tailTrace_6501869
  have hstable : (prefixWord ++ tailWord_6501869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501869).length < 2 ^ (prefixWord ++ tailWord_6501869).sum := by decide
  have hdescent : baseEnd_6501869 < baseStart_6501869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501872 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_6501872 : Nat := 118140960795 + 6501872 * 2 ^ 59
def prefixEnd_6501872 : Nat := 4983230072969 + 3 ^ 40 * 6501872 * 2
def baseEnd_6501872 : Nat := 3338585490009890629598441

theorem tailTrace_6501872 : CollatzResearch.WordTrace tailWord_6501872 prefixEnd_6501872 3338585490009890629598441 := by
  unfold tailWord_6501872
  simp only [CollatzResearch.WordTrace]
  refine ⟨118571376950417825088377935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158095169267223766784503913 118571376950417825088377935)
  ·
    refine ⟨177857065425626737632566903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118571376950417825088377935 177857065425626737632566903)
    ·
      refine ⟨266785598138440106448850355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177857065425626737632566903 266785598138440106448850355)
      ·
        refine ⟨400178397207660159673275533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266785598138440106448850355 400178397207660159673275533)
        ·
          refine ⟨150066898952872559877478325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400178397207660159673275533 150066898952872559877478325)
          ·
            refine ⟨14068771776831802488513593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150066898952872559877478325 14068771776831802488513593)
            ·
              refine ⟨10551578832623851866385195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14068771776831802488513593 10551578832623851866385195)
              ·
                refine ⟨15827368248935777799577793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10551578832623851866385195 15827368248935777799577793)
                ·
                  refine ⟨11870526186701833349683345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15827368248935777799577793 11870526186701833349683345)
                  ·
                    refine ⟨8902894640026375012262509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11870526186701833349683345 8902894640026375012262509)
                    ·
                      refine ⟨3338585490009890629598441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8902894640026375012262509 3338585490009890629598441)
                      ·
                        rfl

theorem cell23_6501872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_6501872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501872 prefixEnd_6501872 := by exact prefixLift 6501872
  have htrace : WordTrace (prefixWord ++ tailWord_6501872) baseStart_6501872 baseEnd_6501872 := by
    simpa [prefixWord, tailWord_6501872, baseEnd_6501872] using wordTrace_append hprefix tailTrace_6501872
  have hstable : (prefixWord ++ tailWord_6501872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501872).length < 2 ^ (prefixWord ++ tailWord_6501872).sum := by decide
  have hdescent : baseEnd_6501872 < baseStart_6501872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501939 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 1, 5]
def baseStart_6501939 : Nat := 118140960795 + 6501939 * 2 ^ 59
def prefixEnd_6501939 : Nat := 4983230072969 + 3 ^ 40 * 6501939 * 2
def baseEnd_6501939 : Nat := 1112873297737913955820211

theorem tailTrace_6501939 : CollatzResearch.WordTrace tailWord_6501939 prefixEnd_6501939 1112873297737913955820211 := by
  unfold tailWord_6501939
  simp only [CollatzResearch.WordTrace]
  refine ⟨237145197591592920619444871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158096798394395280412963247 237145197591592920619444871)
  ·
    refine ⟨355717796387389380929167307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237145197591592920619444871 355717796387389380929167307)
    ·
      refine ⟨533576694581084071393750961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355717796387389380929167307 533576694581084071393750961)
      ·
        refine ⟨400182520935813053545313221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533576694581084071393750961 400182520935813053545313221)
        ·
          refine ⟨75034222675464947539746229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400182520935813053545313221 75034222675464947539746229)
          ·
            refine ⟨7034458375824838831851209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75034222675464947539746229 7034458375824838831851209)
            ·
              refine ⟨5275843781868629123888407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034458375824838831851209 5275843781868629123888407)
              ·
                refine ⟨7913765672802943685832611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275843781868629123888407 7913765672802943685832611)
                ·
                  refine ⟨11870648509204415528748917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7913765672802943685832611 11870648509204415528748917)
                  ·
                    refine ⟨1112873297737913955820211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11870648509204415528748917 1112873297737913955820211)
                    ·
                      rfl

theorem cell23_6501939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 5].length) (baseStart_6501939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501939 prefixEnd_6501939 := by exact prefixLift 6501939
  have htrace : WordTrace (prefixWord ++ tailWord_6501939) baseStart_6501939 baseEnd_6501939 := by
    simpa [prefixWord, tailWord_6501939, baseEnd_6501939] using wordTrace_append hprefix tailTrace_6501939
  have hstable : (prefixWord ++ tailWord_6501939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501939).length < 2 ^ (prefixWord ++ tailWord_6501939).sum := by decide
  have hdescent : baseEnd_6501939 < baseStart_6501939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501969 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 2, 4]
def baseStart_6501969 : Nat := 118140960795 + 6501969 * 2 ^ 59
def prefixEnd_6501969 : Nat := 4983230072969 + 3 ^ 40 * 6501969 * 2
def baseEnd_6501969 : Nat := 1112878432544458916695165

theorem tailTrace_6501969 : CollatzResearch.WordTrace tailWord_6501969 prefixEnd_6501969 1112878432544458916695165 := by
  unfold tailWord_6501969
  simp only [CollatzResearch.WordTrace]
  refine ⟨237146291781484235743036961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158097527854322823828691307 237146291781484235743036961)
  ·
    refine ⟨177859718836113176807277721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237146291781484235743036961 177859718836113176807277721)
    ·
      refine ⟨133394789127084882605458291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177859718836113176807277721 133394789127084882605458291)
      ·
        refine ⟨200092183690627323908187437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133394789127084882605458291 200092183690627323908187437)
        ·
          refine ⟨75034568883985246465570289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200092183690627323908187437 75034568883985246465570289)
          ·
            refine ⟨56275926662988934849177717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75034568883985246465570289 56275926662988934849177717)
            ·
              refine ⟨5275868124655212642110411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56275926662988934849177717 5275868124655212642110411)
              ·
                refine ⟨7913802186982818963165617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275868124655212642110411 7913802186982818963165617)
                ·
                  refine ⟨5935351640237114222374213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913802186982818963165617 5935351640237114222374213)
                  ·
                    refine ⟨1112878432544458916695165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935351640237114222374213 1112878432544458916695165)
                    ·
                      rfl

theorem cell23_6501969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_6501969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501969 prefixEnd_6501969 := by exact prefixLift 6501969
  have htrace : WordTrace (prefixWord ++ tailWord_6501969) baseStart_6501969 baseEnd_6501969 := by
    simpa [prefixWord, tailWord_6501969, baseEnd_6501969] using wordTrace_append hprefix tailTrace_6501969
  have hstable : (prefixWord ++ tailWord_6501969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501969).length < 2 ^ (prefixWord ++ tailWord_6501969).sum := by decide
  have hdescent : baseEnd_6501969 < baseStart_6501969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502009 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 3]
def baseStart_6502009 : Nat := 118140960795 + 6502009 * 2 ^ 59
def prefixEnd_6502009 : Nat := 4983230072969 + 3 ^ 40 * 6502009 * 2
def baseEnd_6502009 : Nat := 3338655836859556593585311

theorem tailTrace_6502009 : CollatzResearch.WordTrace tailWord_6502009 prefixEnd_6502009 3338655836859556593585311 := by
  unfold tailWord_6502009
  simp only [CollatzResearch.WordTrace]
  refine ⟨237147750701339322574493081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158098500467559548382995387 237147750701339322574493081)
  ·
    refine ⟨177860813026004491930869811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237147750701339322574493081 177860813026004491930869811)
    ·
      refine ⟨266791219539006737896304717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177860813026004491930869811 266791219539006737896304717)
      ·
        refine ⟨100046707327127526711114269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266791219539006737896304717 100046707327127526711114269)
        ·
          refine ⟨37517515247672822516667851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100046707327127526711114269 37517515247672822516667851)
          ·
            refine ⟨56276272871509233775001777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37517515247672822516667851 56276272871509233775001777)
            ·
              refine ⟨42207204653631925331251333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56276272871509233775001777 42207204653631925331251333)
              ·
                refine ⟨7913850872555985999609625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42207204653631925331251333 7913850872555985999609625)
                ·
                  refine ⟨5935388154416989499707219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913850872555985999609625 5935388154416989499707219)
                  ·
                    refine ⟨8903082231625484249560829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935388154416989499707219 8903082231625484249560829)
                    ·
                      refine ⟨3338655836859556593585311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8903082231625484249560829 3338655836859556593585311)
                      ·
                        rfl

theorem cell23_6502009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_6502009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502009 prefixEnd_6502009 := by exact prefixLift 6502009
  have htrace : WordTrace (prefixWord ++ tailWord_6502009) baseStart_6502009 baseEnd_6502009 := by
    simpa [prefixWord, tailWord_6502009, baseEnd_6502009] using wordTrace_append hprefix tailTrace_6502009
  have hstable : (prefixWord ++ tailWord_6502009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502009).length < 2 ^ (prefixWord ++ tailWord_6502009).sum := by decide
  have hdescent : baseEnd_6502009 < baseStart_6502009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502025 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_6502025 : Nat := 118140960795 + 6502025 * 2 ^ 59
def prefixEnd_6502025 : Nat := 4983230072969 + 3 ^ 40 * 6502025 * 2
def baseEnd_6502025 : Nat := 1112888017516676176995079

theorem tailTrace_6502025 : CollatzResearch.WordTrace tailWord_6502025 prefixEnd_6502025 1112888017516676176995079 := by
  unfold tailWord_6502025
  simp only [CollatzResearch.WordTrace]
  refine ⟨237148334269281357307075529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158098889512854238204717019 237148334269281357307075529)
  ·
    refine ⟨177861250701961017980306647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237148334269281357307075529 177861250701961017980306647)
    ·
      refine ⟨266791876052941526970459971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177861250701961017980306647 266791876052941526970459971)
      ·
        refine ⟨400187814079412290455689957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266791876052941526970459971 400187814079412290455689957)
        ·
          refine ⟨75035215139889804460441867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400187814079412290455689957 75035215139889804460441867)
          ·
            refine ⟨112552822709834706690662801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75035215139889804460441867 112552822709834706690662801)
            ·
              refine ⟨84414617032376030017997101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112552822709834706690662801 84414617032376030017997101)
              ·
                refine ⟨31655481387141011256748913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84414617032376030017997101 31655481387141011256748913)
                ·
                  refine ⟨23741611040355758442561685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31655481387141011256748913 23741611040355758442561685)
                  ·
                    refine ⟨1112888017516676176995079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23741611040355758442561685 1112888017516676176995079)
                    ·
                      rfl

theorem cell23_6502025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_6502025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502025 prefixEnd_6502025 := by exact prefixLift 6502025
  have htrace : WordTrace (prefixWord ++ tailWord_6502025) baseStart_6502025 baseEnd_6502025 := by
    simpa [prefixWord, tailWord_6502025, baseEnd_6502025] using wordTrace_append hprefix tailTrace_6502025
  have hstable : (prefixWord ++ tailWord_6502025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502025).length < 2 ^ (prefixWord ++ tailWord_6502025).sum := by decide
  have hdescent : baseEnd_6502025 < baseStart_6502025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502026 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_6502026 : Nat := 118140960795 + 6502026 * 2 ^ 59
def prefixEnd_6502026 : Nat := 4983230072969 + 3 ^ 40 * 6502026 * 2
def baseEnd_6502026 : Nat := 3338664566030683027072733

theorem tailTrace_6502026 : CollatzResearch.WordTrace tailWord_6502026 prefixEnd_6502026 3338664566030683027072733 := by
  unfold tailWord_6502026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59287092685569433619465483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158098913828185156318574621 59287092685569433619465483)
  ·
    refine ⟨88930639028354150429198225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59287092685569433619465483 88930639028354150429198225)
    ·
      refine ⟨66697979271265612821898669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88930639028354150429198225 66697979271265612821898669)
      ·
        refine ⟨25011742226724604808212001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66697979271265612821898669 25011742226724604808212001)
        ·
          refine ⟨18758806670043453606159001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25011742226724604808212001 18758806670043453606159001)
          ·
            refine ⟨14069105002532590204619251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18758806670043453606159001 14069105002532590204619251)
            ·
              refine ⟨21103657503798885306928877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14069105002532590204619251 21103657503798885306928877)
              ·
                refine ⟨7913871563924581990098329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21103657503798885306928877 7913871563924581990098329)
                ·
                  refine ⟨5935403672943436492573747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913871563924581990098329 5935403672943436492573747)
                  ·
                    refine ⟨8903105509415154738860621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935403672943436492573747 8903105509415154738860621)
                    ·
                      refine ⟨3338664566030683027072733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8903105509415154738860621 3338664566030683027072733)
                      ·
                        rfl

theorem cell23_6502026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_6502026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502026 prefixEnd_6502026 := by exact prefixLift 6502026
  have htrace : WordTrace (prefixWord ++ tailWord_6502026) baseStart_6502026 baseEnd_6502026 := by
    simpa [prefixWord, tailWord_6502026, baseEnd_6502026] using wordTrace_append hprefix tailTrace_6502026
  have hstable : (prefixWord ++ tailWord_6502026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502026).length < 2 ^ (prefixWord ++ tailWord_6502026).sum := by decide
  have hdescent : baseEnd_6502026 < baseStart_6502026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2]
def baseStart_6502032 : Nat := 118140960795 + 6502032 * 2 ^ 59
def prefixEnd_6502032 : Nat := 4983230072969 + 3 ^ 40 * 6502032 * 2
def baseEnd_6502032 : Nat := 3338667646914610003597705

theorem tailTrace_6502032 : CollatzResearch.WordTrace tailWord_6502032 prefixEnd_6502032 3338667646914610003597705 := by
  unfold tailWord_6502032
  simp only [CollatzResearch.WordTrace]
  refine ⟨118574294790127998751290175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158099059720170665001720233 118574294790127998751290175)
  ·
    refine ⟨177861442185191998126935263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118574294790127998751290175 177861442185191998126935263)
    ·
      refine ⟨266792163277787997190402895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177861442185191998126935263 266792163277787997190402895)
      ·
        refine ⟨400188244916681995785604343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266792163277787997190402895 400188244916681995785604343)
        ·
          refine ⟨600282367375022993678406515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400188244916681995785604343 600282367375022993678406515)
          ·
            refine ⟨900423551062534490517609773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600282367375022993678406515 900423551062534490517609773)
            ·
              refine ⟨337658831648450433944103665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 900423551062534490517609773 337658831648450433944103665)
              ·
                refine ⟨253244123736337825458077749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337658831648450433944103665 253244123736337825458077749)
                ·
                  refine ⟨23741636600281671136694789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253244123736337825458077749 23741636600281671136694789)
                  ·
                    refine ⟨4451556862552813338130273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23741636600281671136694789 4451556862552813338130273)
                    ·
                      refine ⟨3338667646914610003597705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451556862552813338130273 3338667646914610003597705)
                      ·
                        rfl

theorem cell23_6502032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2].length) (baseStart_6502032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502032 prefixEnd_6502032 := by exact prefixLift 6502032
  have htrace : WordTrace (prefixWord ++ tailWord_6502032) baseStart_6502032 baseEnd_6502032 := by
    simpa [prefixWord, tailWord_6502032, baseEnd_6502032] using wordTrace_append hprefix tailTrace_6502032
  have hstable : (prefixWord ++ tailWord_6502032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502032).length < 2 ^ (prefixWord ++ tailWord_6502032).sum := by decide
  have hdescent : baseEnd_6502032 < baseStart_6502032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502049 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6502049 : Nat := 118140960795 + 6502049 * 2 ^ 59
def prefixEnd_6502049 : Nat := 4983230072969 + 3 ^ 40 * 6502049 * 2
def baseEnd_6502049 : Nat := 3338676376085736437085127

theorem tailTrace_6502049 : CollatzResearch.WordTrace tailWord_6502049 prefixEnd_6502049 3338676376085736437085127 := by
  unfold tailWord_6502049
  simp only [CollatzResearch.WordTrace]
  refine ⟨237149209621194409405949201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158099473080796272937299467 237149209621194409405949201)
  ·
    refine ⟨177861907215895807054461901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237149209621194409405949201 177861907215895807054461901)
    ·
      refine ⟨66698215205960927645423213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177861907215895807054461901 66698215205960927645423213)
      ·
        refine ⟨25011830702235347867033705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66698215205960927645423213 25011830702235347867033705)
        ·
          refine ⟨18758873026676510900275279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25011830702235347867033705 18758873026676510900275279)
          ·
            refine ⟨28138309540014766350412919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18758873026676510900275279 28138309540014766350412919)
            ·
              refine ⟨42207464310022149525619379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28138309540014766350412919 42207464310022149525619379)
              ·
                refine ⟨63311196465033224288429069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42207464310022149525619379 63311196465033224288429069)
                ·
                  refine ⟨23741698674387459108160901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63311196465033224288429069 23741698674387459108160901)
                  ·
                    refine ⟨4451568501447648582780169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23741698674387459108160901 4451568501447648582780169)
                    ·
                      refine ⟨3338676376085736437085127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451568501447648582780169 3338676376085736437085127)
                      ·
                        rfl

theorem cell23_6502049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6502049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502049 prefixEnd_6502049 := by exact prefixLift 6502049
  have htrace : WordTrace (prefixWord ++ tailWord_6502049) baseStart_6502049 baseEnd_6502049 := by
    simpa [prefixWord, tailWord_6502049, baseEnd_6502049] using wordTrace_append hprefix tailTrace_6502049
  have hstable : (prefixWord ++ tailWord_6502049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502049).length < 2 ^ (prefixWord ++ tailWord_6502049).sum := by decide
  have hdescent : baseEnd_6502049 < baseStart_6502049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502052 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_6502052 : Nat := 118140960795 + 6502052 * 2 ^ 59
def prefixEnd_6502052 : Nat := 4983230072969 + 3 ^ 40 * 6502052 * 2
def baseEnd_6502052 : Nat := 3338677916527699925347613

theorem tailTrace_6502052 : CollatzResearch.WordTrace tailWord_6502052 prefixEnd_6502052 3338677916527699925347613 := by
  unfold tailWord_6502052
  simp only [CollatzResearch.WordTrace]
  refine ⟨118574659520091770459154205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158099546026789027278872273 118574659520091770459154205)
  ·
    refine ⟨44465497320034413922182827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118574659520091770459154205 44465497320034413922182827)
    ·
      refine ⟨66698245980051620883274241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44465497320034413922182827 66698245980051620883274241)
      ·
        refine ⟨50023684485038715662455681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66698245980051620883274241 50023684485038715662455681)
        ·
          refine ⟨37517763363779036746841761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50023684485038715662455681 37517763363779036746841761)
          ·
            refine ⟨28138322522834277560131321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37517763363779036746841761 28138322522834277560131321)
            ·
              refine ⟨21103741892125708170098491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28138322522834277560131321 21103741892125708170098491)
              ·
                refine ⟨31655612838188562255147737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21103741892125708170098491 31655612838188562255147737)
                ·
                  refine ⟨23741709628641421691360803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31655612838188562255147737 23741709628641421691360803)
                  ·
                    refine ⟨35612564442962132537041205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23741709628641421691360803 35612564442962132537041205)
                    ·
                      refine ⟨3338677916527699925347613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35612564442962132537041205 3338677916527699925347613)
                      ·
                        rfl

theorem cell23_6502052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_6502052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502052 prefixEnd_6502052 := by exact prefixLift 6502052
  have htrace : WordTrace (prefixWord ++ tailWord_6502052) baseStart_6502052 baseEnd_6502052 := by
    simpa [prefixWord, tailWord_6502052, baseEnd_6502052] using wordTrace_append hprefix tailTrace_6502052
  have hstable : (prefixWord ++ tailWord_6502052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502052).length < 2 ^ (prefixWord ++ tailWord_6502052).sum := by decide
  have hdescent : baseEnd_6502052 < baseStart_6502052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502066 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_6502066 : Nat := 118140960795 + 6502066 * 2 ^ 59
def prefixEnd_6502066 : Nat := 4983230072969 + 3 ^ 40 * 6502066 * 2
def baseEnd_6502066 : Nat := 3338685105256862870572549

theorem tailTrace_6502066 : CollatzResearch.WordTrace tailWord_6502066 prefixEnd_6502066 3338685105256862870572549 := by
  unfold tailWord_6502066
  simp only [CollatzResearch.WordTrace]
  refine ⟨59287457415533205327329513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158099886441421880872878701 59287457415533205327329513)
  ·
    refine ⟨44465593061649903995497135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59287457415533205327329513 44465593061649903995497135)
    ·
      refine ⟨66698389592474855993245703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44465593061649903995497135 66698389592474855993245703)
      ·
        refine ⟨100047584388712283989868555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66698389592474855993245703 100047584388712283989868555)
        ·
          refine ⟨150071376583068425984802833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100047584388712283989868555 150071376583068425984802833)
          ·
            refine ⟨112553532437301319488602125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150071376583068425984802833 112553532437301319488602125)
            ·
              refine ⟨42207574663987994808225797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112553532437301319488602125 42207574663987994808225797)
              ·
                refine ⟨7913920249497749026542337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42207574663987994808225797 7913920249497749026542337)
                ·
                  refine ⟨5935440187123311769906753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913920249497749026542337 5935440187123311769906753)
                  ·
                    refine ⟨4451580140342483827430065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5935440187123311769906753 4451580140342483827430065)
                    ·
                      refine ⟨3338685105256862870572549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451580140342483827430065 3338685105256862870572549)
                      ·
                        rfl

theorem cell23_6502066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_6502066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502066 prefixEnd_6502066 := by exact prefixLift 6502066
  have htrace : WordTrace (prefixWord ++ tailWord_6502066) baseStart_6502066 baseEnd_6502066 := by
    simpa [prefixWord, tailWord_6502066, baseEnd_6502066] using wordTrace_append hprefix tailTrace_6502066
  have hstable : (prefixWord ++ tailWord_6502066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502066).length < 2 ^ (prefixWord ++ tailWord_6502066).sum := by decide
  have hdescent : baseEnd_6502066 < baseStart_6502066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502085 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_6502085 : Nat := 118140960795 + 6502085 * 2 ^ 59
def prefixEnd_6502085 : Nat := 4983230072969 + 3 ^ 40 * 6502085 * 2
def baseEnd_6502085 : Nat := 1112898287129766098744987

theorem tailTrace_6502085 : CollatzResearch.WordTrace tailWord_6502085 prefixEnd_6502085 1112898287129766098744987 := by
  unfold tailWord_6502085
  simp only [CollatzResearch.WordTrace]
  refine ⟨237150522649063987554259709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158100348432709325036173139 237150522649063987554259709)
  ·
    refine ⟨88931445993398995332847391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237150522649063987554259709 88931445993398995332847391)
    ·
      refine ⟨133397168990098492999271087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88931445993398995332847391 133397168990098492999271087)
      ·
        refine ⟨200095753485147739498906631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133397168990098492999271087 200095753485147739498906631)
        ·
          refine ⟨300143630227721609248359947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200095753485147739498906631 300143630227721609248359947)
          ·
            refine ⟨450215445341582413872539921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300143630227721609248359947 450215445341582413872539921)
            ·
              refine ⟨337661584006186810404404941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450215445341582413872539921 337661584006186810404404941)
              ·
                refine ⟨126623094002320053901651853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337661584006186810404404941 126623094002320053901651853)
                ·
                  refine ⟨47483660250870020213119445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126623094002320053901651853 47483660250870020213119445)
                  ·
                    refine ⟨1112898287129766098744987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47483660250870020213119445 1112898287129766098744987)
                    ·
                      rfl

theorem cell23_6502085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_6502085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502085 prefixEnd_6502085 := by exact prefixLift 6502085
  have htrace : WordTrace (prefixWord ++ tailWord_6502085) baseStart_6502085 baseEnd_6502085 := by
    simpa [prefixWord, tailWord_6502085, baseEnd_6502085] using wordTrace_append hprefix tailTrace_6502085
  have hstable : (prefixWord ++ tailWord_6502085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502085).length < 2 ^ (prefixWord ++ tailWord_6502085).sum := by decide
  have hdescent : baseEnd_6502085 < baseStart_6502085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502095 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_6502095 : Nat := 118140960795 + 6502095 * 2 ^ 59
def prefixEnd_6502095 : Nat := 4983230072969 + 3 ^ 40 * 6502095 * 2
def baseEnd_6502095 : Nat := 3338699996195843257109915

theorem tailTrace_6502095 : CollatzResearch.WordTrace tailWord_6502095 prefixEnd_6502095 3338699996195843257109915 := by
  unfold tailWord_6502095
  simp only [CollatzResearch.WordTrace]
  refine ⟨237150887379027759262123739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158100591586018506174749159 237150887379027759262123739)
  ·
    refine ⟨355726331068541638893185609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237150887379027759262123739 355726331068541638893185609)
    ·
      refine ⟨266794748301406229169889207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355726331068541638893185609 266794748301406229169889207)
      ·
        refine ⟨400192122452109343754833811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266794748301406229169889207 400192122452109343754833811)
        ·
          refine ⟨600288183678164015632250717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400192122452109343754833811 600288183678164015632250717)
          ·
            refine ⟨225108068879311505862094019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600288183678164015632250717 225108068879311505862094019)
            ·
              refine ⟨337662103318967258793141029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225108068879311505862094019 337662103318967258793141029)
              ·
                refine ⟨63311644372306361023713943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337662103318967258793141029 63311644372306361023713943)
                ·
                  refine ⟨94967466558459541535570915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63311644372306361023713943 94967466558459541535570915)
                  ·
                    refine ⟨142451199837689312303356373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94967466558459541535570915 142451199837689312303356373)
                    ·
                      refine ⟨3338699996195843257109915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142451199837689312303356373 3338699996195843257109915)
                      ·
                        rfl

theorem cell23_6502095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_6502095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502095 prefixEnd_6502095 := by exact prefixLift 6502095
  have htrace : WordTrace (prefixWord ++ tailWord_6502095) baseStart_6502095 baseEnd_6502095 := by
    simpa [prefixWord, tailWord_6502095, baseEnd_6502095] using wordTrace_append hprefix tailTrace_6502095
  have hstable : (prefixWord ++ tailWord_6502095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502095).length < 2 ^ (prefixWord ++ tailWord_6502095).sum := by decide
  have hdescent : baseEnd_6502095 < baseStart_6502095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502152 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_6502152 : Nat := 118140960795 + 6502152 * 2 ^ 59
def prefixEnd_6502152 : Nat := 4983230072969 + 3 ^ 40 * 6502152 * 2
def baseEnd_6502152 : Nat := 3338729264593149534097153

theorem tailTrace_6502152 : CollatzResearch.WordTrace tailWord_6502152 prefixEnd_6502152 3338729264593149534097153 := by
  unfold tailWord_6502152
  simp only [CollatzResearch.WordTrace]
  refine ⟨118576483169910628998474355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158101977559880838664632473 118576483169910628998474355)
  ·
    refine ⟨177864724754865943497711533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118576483169910628998474355 177864724754865943497711533)
    ·
      refine ⟨66699271783074728811641825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177864724754865943497711533 66699271783074728811641825)
      ·
        refine ⟨50024453837306046608731369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66699271783074728811641825 50024453837306046608731369)
        ·
          refine ⟨37518340377979534956548527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50024453837306046608731369 37518340377979534956548527)
          ·
            refine ⟨56277510566969302434822791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37518340377979534956548527 56277510566969302434822791)
            ·
              refine ⟨84416265850453953652234187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56277510566969302434822791 84416265850453953652234187)
              ·
                refine ⟨126624398775680930478351281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84416265850453953652234187 126624398775680930478351281)
                ·
                  refine ⟨94968299081760697858763461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126624398775680930478351281 94968299081760697858763461)
                  ·
                    refine ⟨17806556077830130848518149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94968299081760697858763461 17806556077830130848518149)
                    ·
                      refine ⟨3338729264593149534097153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17806556077830130848518149 3338729264593149534097153)
                      ·
                        rfl

theorem cell23_6502152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_6502152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502152 prefixEnd_6502152 := by exact prefixLift 6502152
  have htrace : WordTrace (prefixWord ++ tailWord_6502152) baseStart_6502152 baseEnd_6502152 := by
    simpa [prefixWord, tailWord_6502152, baseEnd_6502152] using wordTrace_append hprefix tailTrace_6502152
  have hstable : (prefixWord ++ tailWord_6502152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502152).length < 2 ^ (prefixWord ++ tailWord_6502152).sum := by decide
  have hdescent : baseEnd_6502152 < baseStart_6502152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502196 : List Nat := [2, 5, 1, 1, 2, 2, 1, 3, 6]
def baseStart_6502196 : Nat := 118140960795 + 6502196 * 2 ^ 59
def prefixEnd_6502196 : Nat := 4983230072969 + 3 ^ 40 * 6502196 * 2
def baseEnd_6502196 : Nat := 370972428637994151327439

theorem tailTrace_6502196 : CollatzResearch.WordTrace tailWord_6502196 prefixEnd_6502196 370972428637994151327439 := by
  unfold tailWord_6502196
  simp only [CollatzResearch.WordTrace]
  refine ⟨118577285575830926755775221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158103047434441235674366961 118577285575830926755775221)
  ·
    refine ⟨11116620522734149383353927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118577285575830926755775221 11116620522734149383353927)
    ·
      refine ⟨16674930784101224075030891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11116620522734149383353927 16674930784101224075030891)
      ·
        refine ⟨25012396176151836112546337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16674930784101224075030891 25012396176151836112546337)
        ·
          refine ⟨18759297132113877084409753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25012396176151836112546337 18759297132113877084409753)
          ·
            refine ⟨14069472849085407813307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18759297132113877084409753 14069472849085407813307315)
            ·
              refine ⟨21104209273628111719960973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14069472849085407813307315 21104209273628111719960973)
              ·
                refine ⟨7914078477610541894985365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21104209273628111719960973 7914078477610541894985365)
                ·
                  refine ⟨370972428637994151327439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7914078477610541894985365 370972428637994151327439)
                  ·
                    rfl

theorem cell23_6502196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_6502196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502196 prefixEnd_6502196 := by exact prefixLift 6502196
  have htrace : WordTrace (prefixWord ++ tailWord_6502196) baseStart_6502196 baseEnd_6502196 := by
    simpa [prefixWord, tailWord_6502196, baseEnd_6502196] using wordTrace_append hprefix tailTrace_6502196
  have hstable : (prefixWord ++ tailWord_6502196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502196).length < 2 ^ (prefixWord ++ tailWord_6502196).sum := by decide
  have hdescent : baseEnd_6502196 < baseStart_6502196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502199 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_6502199 : Nat := 118140960795 + 6502199 * 2 ^ 59
def prefixEnd_6502199 : Nat := 4983230072969 + 3 ^ 40 * 6502199 * 2
def baseEnd_6502199 : Nat := 3338753398183910850209437

theorem tailTrace_6502199 : CollatzResearch.WordTrace tailWord_6502199 prefixEnd_6502199 3338753398183910850209437 := by
  unfold tailWord_6502199
  simp only [CollatzResearch.WordTrace]
  refine ⟨237154680570650985023909651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158103120380433990015939767 237154680570650985023909651)
  ·
    refine ⟨355732020855976477535864477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237154680570650985023909651 355732020855976477535864477)
    ·
      refine ⟨133399507820991179075949179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355732020855976477535864477 133399507820991179075949179)
      ·
        refine ⟨200099261731486768613923769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133399507820991179075949179 200099261731486768613923769)
        ·
          refine ⟨150074446298615076460442827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200099261731486768613923769 150074446298615076460442827)
          ·
            refine ⟨225111669447922614690664241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150074446298615076460442827 225111669447922614690664241)
            ·
              refine ⟨168833752085941961017998181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225111669447922614690664241 168833752085941961017998181)
              ·
                refine ⟨31656328516114117690874659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168833752085941961017998181 31656328516114117690874659)
                ·
                  refine ⟨47484492774171176536311989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31656328516114117690874659 47484492774171176536311989)
                  ·
                    refine ⟨4451671197578547800279249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47484492774171176536311989 4451671197578547800279249)
                    ·
                      refine ⟨3338753398183910850209437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451671197578547800279249 3338753398183910850209437)
                      ·
                        rfl

theorem cell23_6502199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_6502199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502199 prefixEnd_6502199 := by exact prefixLift 6502199
  have htrace : WordTrace (prefixWord ++ tailWord_6502199) baseStart_6502199 baseEnd_6502199 := by
    simpa [prefixWord, tailWord_6502199, baseEnd_6502199] using wordTrace_append hprefix tailTrace_6502199
  have hstable : (prefixWord ++ tailWord_6502199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502199).length < 2 ^ (prefixWord ++ tailWord_6502199).sum := by decide
  have hdescent : baseEnd_6502199 < baseStart_6502199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502216 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_6502216 : Nat := 118140960795 + 6502216 * 2 ^ 59
def prefixEnd_6502216 : Nat := 4983230072969 + 3 ^ 40 * 6502216 * 2
def baseEnd_6502216 : Nat := 3338762127355037283696859

theorem tailTrace_6502216 : CollatzResearch.WordTrace tailWord_6502216 prefixEnd_6502216 3338762127355037283696859 := by
  unfold tailWord_6502216
  simp only [CollatzResearch.WordTrace]
  refine ⟨118577650305794698463639251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158103533741059597951519001 118577650305794698463639251)
  ·
    refine ⟨177866475458692047695458877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118577650305794698463639251 177866475458692047695458877)
    ·
      refine ⟨66699928297009517885797079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177866475458692047695458877 66699928297009517885797079)
      ·
        refine ⟨100049892445514276828695619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66699928297009517885797079 100049892445514276828695619)
        ·
          refine ⟨150074838668271415243043429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100049892445514276828695619 150074838668271415243043429)
          ·
            refine ⟨28139032250300890358070643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150074838668271415243043429 28139032250300890358070643)
            ·
              refine ⟨42208548375451335537105965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28139032250300890358070643 42208548375451335537105965)
              ·
                refine ⟨15828205640794250826414737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42208548375451335537105965 15828205640794250826414737)
                ·
                  refine ⟨11871154230595688119811053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15828205640794250826414737 11871154230595688119811053)
                  ·
                    refine ⟨4451682836473383044929145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11871154230595688119811053 4451682836473383044929145)
                    ·
                      refine ⟨3338762127355037283696859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451682836473383044929145 3338762127355037283696859)
                      ·
                        rfl

theorem cell23_6502216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_6502216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502216 prefixEnd_6502216 := by exact prefixLift 6502216
  have htrace : WordTrace (prefixWord ++ tailWord_6502216) baseStart_6502216 baseEnd_6502216 := by
    simpa [prefixWord, tailWord_6502216, baseEnd_6502216] using wordTrace_append hprefix tailTrace_6502216
  have hstable : (prefixWord ++ tailWord_6502216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502216).length < 2 ^ (prefixWord ++ tailWord_6502216).sum := by decide
  have hdescent : baseEnd_6502216 < baseStart_6502216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502240 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 1, 1, 3]
def baseStart_6502240 : Nat := 118140960795 + 6502240 * 2 ^ 59
def prefixEnd_6502240 : Nat := 4983230072969 + 3 ^ 40 * 6502240 * 2
def baseEnd_6502240 : Nat := 3338774450890745189796749

theorem tailTrace_6502240 : CollatzResearch.WordTrace tailWord_6502240 prefixEnd_6502240 3338774450890745189796749 := by
  unfold tailWord_6502240
  simp only [CollatzResearch.WordTrace]
  refine ⟨118578087981751224513076087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158104117309001632684101449 118578087981751224513076087)
  ·
    refine ⟨177867131972626836769614131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118578087981751224513076087 177867131972626836769614131)
    ·
      refine ⟨266800697958940255154421197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177867131972626836769614131 266800697958940255154421197)
      ·
        refine ⟨100050261734602595682907949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266800697958940255154421197 100050261734602595682907949)
        ·
          refine ⟨37518848150475973381090481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100050261734602595682907949 37518848150475973381090481)
          ·
            refine ⟨28139136112856980035817861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37518848150475973381090481 28139136112856980035817861)
            ·
              refine ⟨5276088021160683756715849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28139136112856980035817861 5276088021160683756715849)
              ·
                refine ⟨3957066015870512817536887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276088021160683756715849 3957066015870512817536887)
                ·
                  refine ⟨5935599023805769226305331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957066015870512817536887 5935599023805769226305331)
                  ·
                    refine ⟨8903398535708653839457997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935599023805769226305331 8903398535708653839457997)
                    ·
                      refine ⟨3338774450890745189796749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8903398535708653839457997 3338774450890745189796749)
                      ·
                        rfl

theorem cell23_6502240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_6502240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502240 prefixEnd_6502240 := by exact prefixLift 6502240
  have htrace : WordTrace (prefixWord ++ tailWord_6502240) baseStart_6502240 baseEnd_6502240 := by
    simpa [prefixWord, tailWord_6502240, baseEnd_6502240] using wordTrace_append hprefix tailTrace_6502240
  have hstable : (prefixWord ++ tailWord_6502240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502240).length < 2 ^ (prefixWord ++ tailWord_6502240).sum := by decide
  have hdescent : baseEnd_6502240 < baseStart_6502240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502280 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6502280 : Nat := 118140960795 + 6502280 * 2 ^ 59
def prefixEnd_6502280 : Nat := 4983230072969 + 3 ^ 40 * 6502280 * 2
def baseEnd_6502280 : Nat := 3338794990116925033296565

theorem tailTrace_6502280 : CollatzResearch.WordTrace tailWord_6502280 prefixEnd_6502280 3338794990116925033296565 := by
  unfold tailWord_6502280
  simp only [CollatzResearch.WordTrace]
  refine ⟨118578817441678767928804147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158105089922238357238405529 118578817441678767928804147)
  ·
    refine ⟨177868226162518151893206221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118578817441678767928804147 177868226162518151893206221)
    ·
      refine ⟨66700584810944306959952333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177868226162518151893206221 66700584810944306959952333)
      ·
        refine ⟨25012719304104115109982125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66700584810944306959952333 25012719304104115109982125)
        ·
          refine ⟨9379769739039043166243297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25012719304104115109982125 9379769739039043166243297)
          ·
            refine ⟨7034827304279282374682473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9379769739039043166243297 7034827304279282374682473)
            ·
              refine ⟨5276120478209461781011855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034827304279282374682473 5276120478209461781011855)
              ·
                refine ⟨7914180717314192671517783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276120478209461781011855 7914180717314192671517783)
                ·
                  refine ⟨11871271075971289007276675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7914180717314192671517783 11871271075971289007276675)
                  ·
                    refine ⟨17806906613956933510915013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11871271075971289007276675 17806906613956933510915013)
                    ·
                      refine ⟨3338794990116925033296565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17806906613956933510915013 3338794990116925033296565)
                      ·
                        rfl

theorem cell23_6502280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6502280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502280 prefixEnd_6502280 := by exact prefixLift 6502280
  have htrace : WordTrace (prefixWord ++ tailWord_6502280) baseStart_6502280 baseEnd_6502280 := by
    simpa [prefixWord, tailWord_6502280, baseEnd_6502280] using wordTrace_append hprefix tailTrace_6502280
  have hstable : (prefixWord ++ tailWord_6502280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502280).length < 2 ^ (prefixWord ++ tailWord_6502280).sum := by decide
  have hdescent : baseEnd_6502280 < baseStart_6502280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502286 : List Nat := [4, 1, 1, 5, 1, 1, 10]
def baseStart_6502286 : Nat := 118140960795 + 6502286 * 2 ^ 59
def prefixEnd_6502286 : Nat := 4983230072969 + 3 ^ 40 * 6502286 * 2
def baseEnd_6502286 : Nat := 41219729271615456911377

theorem tailTrace_6502286 : CollatzResearch.WordTrace tailWord_6502286 prefixEnd_6502286 41219729271615456911377 := by
  unfold tailWord_6502286
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644731715166974860290839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158105235814223865921551141 29644731715166974860290839)
  ·
    refine ⟨44467097572750462290436259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29644731715166974860290839 44467097572750462290436259)
    ·
      refine ⟨66700646359125693435654389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44467097572750462290436259 66700646359125693435654389)
      ·
        refine ⟨6253185596168033759592599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66700646359125693435654389 6253185596168033759592599)
        ·
          refine ⟨9379778394252050639388899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253185596168033759592599 9379778394252050639388899)
          ·
            refine ⟨14069667591378075959083349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9379778394252050639388899 14069667591378075959083349)
            ·
              refine ⟨41219729271615456911377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14069667591378075959083349 41219729271615456911377)
              ·
                rfl

theorem cell23_6502286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 10].length) (baseStart_6502286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502286 prefixEnd_6502286 := by exact prefixLift 6502286
  have htrace : WordTrace (prefixWord ++ tailWord_6502286) baseStart_6502286 baseEnd_6502286 := by
    simpa [prefixWord, tailWord_6502286, baseEnd_6502286] using wordTrace_append hprefix tailTrace_6502286
  have hstable : (prefixWord ++ tailWord_6502286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502286).length < 2 ^ (prefixWord ++ tailWord_6502286).sum := by decide
  have hdescent : baseEnd_6502286 < baseStart_6502286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502290 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_6502290 : Nat := 118140960795 + 6502290 * 2 ^ 59
def prefixEnd_6502290 : Nat := 4983230072969 + 3 ^ 40 * 6502290 * 2
def baseEnd_6502290 : Nat := 1112933374974489998057173

theorem tailTrace_6502290 : CollatzResearch.WordTrace tailWord_6502290 prefixEnd_6502290 1112933374974489998057173 := by
  unfold tailWord_6502290
  simp only [CollatzResearch.WordTrace]
  refine ⟨59289499903330326891368081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158105333075547538376981549 59289499903330326891368081)
  ·
    refine ⟨44467124927497745168526061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59289499903330326891368081 44467124927497745168526061)
    ·
      refine ⟨16675171847811654438197273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44467124927497745168526061 16675171847811654438197273)
      ·
        refine ⟨12506378885858740828647955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16675171847811654438197273 12506378885858740828647955)
        ·
          refine ⟨18759568328788111242971933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12506378885858740828647955 18759568328788111242971933)
          ·
            refine ⟨7034838123295541716114475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18759568328788111242971933 7034838123295541716114475)
            ·
              refine ⟨10552257184943312574171713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034838123295541716114475 10552257184943312574171713)
              ·
                refine ⟨7914192888707484430628785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10552257184943312574171713 7914192888707484430628785)
                ·
                  refine ⟨5935644666530613322971589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914192888707484430628785 5935644666530613322971589)
                  ·
                    refine ⟨1112933374974489998057173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935644666530613322971589 1112933374974489998057173)
                    ·
                      rfl

theorem cell23_6502290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_6502290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502290 prefixEnd_6502290 := by exact prefixLift 6502290
  have htrace : WordTrace (prefixWord ++ tailWord_6502290) baseStart_6502290 baseEnd_6502290 := by
    simpa [prefixWord, tailWord_6502290, baseEnd_6502290] using wordTrace_append hprefix tailTrace_6502290
  have hstable : (prefixWord ++ tailWord_6502290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502290).length < 2 ^ (prefixWord ++ tailWord_6502290).sum := by decide
  have hdescent : baseEnd_6502290 < baseStart_6502290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502323 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 1, 3, 2]
def baseStart_6502323 : Nat := 118140960795 + 6502323 * 2 ^ 59
def prefixEnd_6502323 : Nat := 4983230072969 + 3 ^ 40 * 6502323 * 2
def baseEnd_6502323 : Nat := 3338817069785068365058867

theorem tailTrace_6502323 : CollatzResearch.WordTrace tailWord_6502323 prefixEnd_6502323 3338817069785068365058867 := by
  unfold tailWord_6502323
  simp only [CollatzResearch.WordTrace]
  refine ⟨237159203222201754201423623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158106135481467836134282415 237159203222201754201423623)
  ·
    refine ⟨355738804833302631302135435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237159203222201754201423623 355738804833302631302135435)
    ·
      refine ⟨533608207249953946953203153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355738804833302631302135435 533608207249953946953203153)
      ·
        refine ⟨400206155437465460214902365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533608207249953946953203153 400206155437465460214902365)
        ·
          refine ⟨150077308289049547580588387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400206155437465460214902365 150077308289049547580588387)
          ·
            refine ⟨225115962433574321370882581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150077308289049547580588387 225115962433574321370882581)
            ·
              refine ⟨10552310739073796314260121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225115962433574321370882581 10552310739073796314260121)
              ·
                refine ⟨7914233054305347235695091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10552310739073796314260121 7914233054305347235695091)
                ·
                  refine ⟨11871349581458020853542637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7914233054305347235695091 11871349581458020853542637)
                  ·
                    refine ⟨4451756093046757820078489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11871349581458020853542637 4451756093046757820078489)
                    ·
                      refine ⟨3338817069785068365058867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451756093046757820078489 3338817069785068365058867)
                      ·
                        rfl

theorem cell23_6502323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3, 2].length) (baseStart_6502323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502323 prefixEnd_6502323 := by exact prefixLift 6502323
  have htrace : WordTrace (prefixWord ++ tailWord_6502323) baseStart_6502323 baseEnd_6502323 := by
    simpa [prefixWord, tailWord_6502323, baseEnd_6502323] using wordTrace_append hprefix tailTrace_6502323
  have hstable : (prefixWord ++ tailWord_6502323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502323).length < 2 ^ (prefixWord ++ tailWord_6502323).sum := by decide
  have hdescent : baseEnd_6502323 < baseStart_6502323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502336 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2]
def baseStart_6502336 : Nat := 118140960795 + 6502336 * 2 ^ 59
def prefixEnd_6502336 : Nat := 4983230072969 + 3 ^ 40 * 6502336 * 2
def baseEnd_6502336 : Nat := 3338823745033576814196307

theorem tailTrace_6502336 : CollatzResearch.WordTrace tailWord_6502336 prefixEnd_6502336 3338823745033576814196307 := by
  unfold tailWord_6502336
  simp only [CollatzResearch.WordTrace]
  refine ⟨118579838685577328710823431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158106451580769771614431241 118579838685577328710823431)
  ·
    refine ⟨177869758028365993066235147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118579838685577328710823431 177869758028365993066235147)
    ·
      refine ⟨266804637042548989599352721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177869758028365993066235147 266804637042548989599352721)
      ·
        refine ⟨200103477781911742199514541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266804637042548989599352721 200103477781911742199514541)
        ·
          refine ⟨75038804168216903324817953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200103477781911742199514541 75038804168216903324817953)
          ·
            refine ⟨56279103126162677493613465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75038804168216903324817953 56279103126162677493613465)
            ·
              refine ⟨42209327344622008120210099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56279103126162677493613465 42209327344622008120210099)
              ·
                refine ⟨63313991016933012180315149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42209327344622008120210099 63313991016933012180315149)
                ·
                  refine ⟨23742746631349879567618181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63313991016933012180315149 23742746631349879567618181)
                  ·
                    refine ⟨4451764993378102418928409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23742746631349879567618181 4451764993378102418928409)
                    ·
                      refine ⟨3338823745033576814196307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451764993378102418928409 3338823745033576814196307)
                      ·
                        rfl

theorem cell23_6502336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_6502336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502336 prefixEnd_6502336 := by exact prefixLift 6502336
  have htrace : WordTrace (prefixWord ++ tailWord_6502336) baseStart_6502336 baseEnd_6502336 := by
    simpa [prefixWord, tailWord_6502336, baseEnd_6502336] using wordTrace_append hprefix tailTrace_6502336
  have hstable : (prefixWord ++ tailWord_6502336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502336).length < 2 ^ (prefixWord ++ tailWord_6502336).sum := by decide
  have hdescent : baseEnd_6502336 < baseStart_6502336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502356 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6502356 : Nat := 118140960795 + 6502356 * 2 ^ 59
def prefixEnd_6502356 : Nat := 4983230072969 + 3 ^ 40 * 6502356 * 2
def baseEnd_6502356 : Nat := 3338834014646666735946215

theorem tailTrace_6502356 : CollatzResearch.WordTrace tailWord_6502356 prefixEnd_6502356 3338834014646666735946215 := by
  unfold tailWord_6502356
  simp only [CollatzResearch.WordTrace]
  refine ⟨118580203415541100418687461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158106937887388133891583281 118580203415541100418687461)
  ·
    refine ⟨22233788140413956328503899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118580203415541100418687461 22233788140413956328503899)
    ·
      refine ⟨33350682210620934492755849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22233788140413956328503899 33350682210620934492755849)
      ·
        refine ⟨25013011657965700869566887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33350682210620934492755849 25013011657965700869566887)
        ·
          refine ⟨37519517486948551304350331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25013011657965700869566887 37519517486948551304350331)
          ·
            refine ⟨56279276230422826956525497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37519517486948551304350331 56279276230422826956525497)
            ·
              refine ⟨42209457172817120217394123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56279276230422826956525497 42209457172817120217394123)
              ·
                refine ⟨63314185759225680326091185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42209457172817120217394123 63314185759225680326091185)
                ·
                  refine ⟨47485639319419260244568389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63314185759225680326091185 47485639319419260244568389)
                  ·
                    refine ⟨8903557372391111295856573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47485639319419260244568389 8903557372391111295856573)
                    ·
                      refine ⟨3338834014646666735946215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8903557372391111295856573 3338834014646666735946215)
                      ·
                        rfl

theorem cell23_6502356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6502356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502356 prefixEnd_6502356 := by exact prefixLift 6502356
  have htrace : WordTrace (prefixWord ++ tailWord_6502356) baseStart_6502356 baseEnd_6502356 := by
    simpa [prefixWord, tailWord_6502356, baseEnd_6502356] using wordTrace_append hprefix tailTrace_6502356
  have hstable : (prefixWord ++ tailWord_6502356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502356).length < 2 ^ (prefixWord ++ tailWord_6502356).sum := by decide
  have hdescent : baseEnd_6502356 < baseStart_6502356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502364 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6502364 : Nat := 118140960795 + 6502364 * 2 ^ 59
def prefixEnd_6502364 : Nat := 4983230072969 + 3 ^ 40 * 6502364 * 2
def baseEnd_6502364 : Nat := 3338838122491902704646179

theorem tailTrace_6502364 : CollatzResearch.WordTrace tailWord_6502364 prefixEnd_6502364 3338838122491902704646179 := by
  unfold tailWord_6502364
  simp only [CollatzResearch.WordTrace]
  refine ⟨118580349307526609101833073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158107132410035478802444097 118580349307526609101833073)
  ·
    refine ⟨88935261980644956826374805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118580349307526609101833073 88935261980644956826374805)
    ·
      refine ⟨4168840405342732351236319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88935261980644956826374805 4168840405342732351236319)
      ·
        refine ⟨6253260608014098526854479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168840405342732351236319 6253260608014098526854479)
        ·
          refine ⟨9379890912021147790281719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253260608014098526854479 9379890912021147790281719)
          ·
            refine ⟨14069836368031721685422579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9379890912021147790281719 14069836368031721685422579)
            ·
              refine ⟨21104754552047582528133869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14069836368031721685422579 21104754552047582528133869)
              ·
                refine ⟨7914282957017843448050201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21104754552047582528133869 7914282957017843448050201)
                ·
                  refine ⟨5935712217763382586037651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914282957017843448050201 5935712217763382586037651)
                  ·
                    refine ⟨8903568326645073879056477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935712217763382586037651 8903568326645073879056477)
                    ·
                      refine ⟨3338838122491902704646179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8903568326645073879056477 3338838122491902704646179)
                      ·
                        rfl

theorem cell23_6502364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6502364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502364 prefixEnd_6502364 := by exact prefixLift 6502364
  have htrace : WordTrace (prefixWord ++ tailWord_6502364) baseStart_6502364 baseEnd_6502364 := by
    simpa [prefixWord, tailWord_6502364, baseEnd_6502364] using wordTrace_append hprefix tailTrace_6502364
  have hstable : (prefixWord ++ tailWord_6502364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502364).length < 2 ^ (prefixWord ++ tailWord_6502364).sum := by decide
  have hdescent : baseEnd_6502364 < baseStart_6502364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502404 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6502404 : Nat := 118140960795 + 6502404 * 2 ^ 59
def prefixEnd_6502404 : Nat := 4983230072969 + 3 ^ 40 * 6502404 * 2
def baseEnd_6502404 : Nat := 3338858661718082548145995

theorem tailTrace_6502404 : CollatzResearch.WordTrace tailWord_6502404 prefixEnd_6502404 3338858661718082548145995 := by
  unfold tailWord_6502404
  simp only [CollatzResearch.WordTrace]
  refine ⟨118581078767454152517561133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158108105023272203356748177 118581078767454152517561133)
  ·
    refine ⟨44467904537795307194085425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118581078767454152517561133 44467904537795307194085425)
    ·
      refine ⟨33350928403346480395564069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44467904537795307194085425 33350928403346480395564069)
      ·
        refine ⟨6253299075627465074168263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33350928403346480395564069 6253299075627465074168263)
        ·
          refine ⟨9379948613441197611252395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253299075627465074168263 9379948613441197611252395)
          ·
            refine ⟨14069922920161796416878593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9379948613441197611252395 14069922920161796416878593)
            ·
              refine ⟨10552442190121347312658945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14069922920161796416878593 10552442190121347312658945)
              ·
                refine ⟨7914331642591010484494209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10552442190121347312658945 7914331642591010484494209)
                ·
                  refine ⟨5935748731943257863370657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914331642591010484494209 5935748731943257863370657)
                  ·
                    refine ⟨4451811548957443397527993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5935748731943257863370657 4451811548957443397527993)
                    ·
                      refine ⟨3338858661718082548145995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451811548957443397527993 3338858661718082548145995)
                      ·
                        rfl

theorem cell23_6502404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6502404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502404 prefixEnd_6502404 := by exact prefixLift 6502404
  have htrace : WordTrace (prefixWord ++ tailWord_6502404) baseStart_6502404 baseEnd_6502404 := by
    simpa [prefixWord, tailWord_6502404, baseEnd_6502404] using wordTrace_append hprefix tailTrace_6502404
  have hstable : (prefixWord ++ tailWord_6502404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502404).length < 2 ^ (prefixWord ++ tailWord_6502404).sum := by decide
  have hdescent : baseEnd_6502404 < baseStart_6502404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502409 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_6502409 : Nat := 118140960795 + 6502409 * 2 ^ 59
def prefixEnd_6502409 : Nat := 4983230072969 + 3 ^ 40 * 6502409 * 2
def baseEnd_6502409 : Nat := 3338861229121355028583471

theorem tailTrace_6502409 : CollatzResearch.WordTrace tailWord_6502409 prefixEnd_6502409 3338861229121355028583471 := by
  unfold tailWord_6502409
  simp only [CollatzResearch.WordTrace]
  refine ⟨237162339899890190889054281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158108226599926793926036187 237162339899890190889054281)
  ·
    refine ⟨177871754924917643166790711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237162339899890190889054281 177871754924917643166790711)
    ·
      refine ⟨266807632387376464750186067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177871754924917643166790711 266807632387376464750186067)
      ·
        refine ⟨400211448581064697125279101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266807632387376464750186067 400211448581064697125279101)
        ·
          refine ⟨150079293217899261421979663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400211448581064697125279101 150079293217899261421979663)
          ·
            refine ⟨225118939826848892132969495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150079293217899261421979663 225118939826848892132969495)
            ·
              refine ⟨337678409740273338199454243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225118939826848892132969495 337678409740273338199454243)
              ·
                refine ⟨506517614610410007299181365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337678409740273338199454243 506517614610410007299181365)
                ·
                  refine ⟨47486026369725938184298253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 506517614610410007299181365 47486026369725938184298253)
                  ·
                    refine ⟨17807259888647226819111845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47486026369725938184298253 17807259888647226819111845)
                    ·
                      refine ⟨3338861229121355028583471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17807259888647226819111845 3338861229121355028583471)
                      ·
                        rfl

theorem cell23_6502409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_6502409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502409 prefixEnd_6502409 := by exact prefixLift 6502409
  have htrace : WordTrace (prefixWord ++ tailWord_6502409) baseStart_6502409 baseEnd_6502409 := by
    simpa [prefixWord, tailWord_6502409, baseEnd_6502409] using wordTrace_append hprefix tailTrace_6502409
  have hstable : (prefixWord ++ tailWord_6502409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502409).length < 2 ^ (prefixWord ++ tailWord_6502409).sum := by decide
  have hdescent : baseEnd_6502409 < baseStart_6502409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502503 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_6502503 : Nat := 118140960795 + 6502503 * 2 ^ 59
def prefixEnd_6502503 : Nat := 4983230072969 + 3 ^ 40 * 6502503 * 2
def baseEnd_6502503 : Nat := 3338909496302877660808039

theorem tailTrace_6502503 : CollatzResearch.WordTrace tailWord_6502503 prefixEnd_6502503 3338909496302877660808039 := by
  unfold tailWord_6502503
  simp only [CollatzResearch.WordTrace]
  refine ⟨237165768361549644942976163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158110512241033096628650775 237165768361549644942976163)
  ·
    refine ⟨355748652542324467414464245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237165768361549644942976163 355748652542324467414464245)
    ·
      refine ⟨33351436175842918820106023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355748652542324467414464245 33351436175842918820106023)
      ·
        refine ⟨50027154263764378230159035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33351436175842918820106023 50027154263764378230159035)
        ·
          refine ⟨75040731395646567345238553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50027154263764378230159035 75040731395646567345238553)
          ·
            refine ⟨56280548546734925508928915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75040731395646567345238553 56280548546734925508928915)
            ·
              refine ⟨84420822820102388263393373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56280548546734925508928915 84420822820102388263393373)
              ·
                refine ⟨31657808557538395598772515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84420822820102388263393373 31657808557538395598772515)
                ·
                  refine ⟨47486712836307593398158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31657808557538395598772515 47486712836307593398158773)
                  ·
                    refine ⟨4451879328403836881077385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47486712836307593398158773 4451879328403836881077385)
                    ·
                      refine ⟨3338909496302877660808039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4451879328403836881077385 3338909496302877660808039)
                      ·
                        rfl

theorem cell23_6502503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_6502503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502503 prefixEnd_6502503 := by exact prefixLift 6502503
  have htrace : WordTrace (prefixWord ++ tailWord_6502503) baseStart_6502503 baseEnd_6502503 := by
    simpa [prefixWord, tailWord_6502503, baseEnd_6502503] using wordTrace_append hprefix tailTrace_6502503
  have hstable : (prefixWord ++ tailWord_6502503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502503).length < 2 ^ (prefixWord ++ tailWord_6502503).sum := by decide
  have hdescent : baseEnd_6502503 < baseStart_6502503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502556 : List Nat := [2, 2, 3, 2, 1, 1, 1, 11]
def baseStart_6502556 : Nat := 118140960795 + 6502556 * 2 ^ 59
def prefixEnd_6502556 : Nat := 4983230072969 + 3 ^ 40 * 6502556 * 2
def baseEnd_6502556 : Nat := 123664322621391331609085

theorem tailTrace_6502556 : CollatzResearch.WordTrace tailWord_6502556 prefixEnd_6502556 123664322621391331609085 := by
  unfold tailWord_6502556
  simp only [CollatzResearch.WordTrace]
  refine ⟨118583850715178817497327761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158111800953571756663103681 118583850715178817497327761)
  ·
    refine ⟨88937888036384113122995821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118583850715178817497327761 88937888036384113122995821)
    ·
      refine ⟨33351708013644042421123433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88937888036384113122995821 33351708013644042421123433)
      ·
        refine ⟨25013781010233031815842575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33351708013644042421123433 25013781010233031815842575)
        ·
          refine ⟨37520671515349547723763863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25013781010233031815842575 37520671515349547723763863)
          ·
            refine ⟨56281007273024321585645795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37520671515349547723763863 56281007273024321585645795)
            ·
              refine ⟨84421510909536482378468693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56281007273024321585645795 84421510909536482378468693)
              ·
                refine ⟨123664322621391331609085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84421510909536482378468693 123664322621391331609085)
                ·
                  rfl

theorem cell23_6502556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 11].length) (baseStart_6502556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502556 prefixEnd_6502556 := by exact prefixLift 6502556
  have htrace : WordTrace (prefixWord ++ tailWord_6502556) baseStart_6502556 baseEnd_6502556 := by
    simpa [prefixWord, tailWord_6502556, baseEnd_6502556] using wordTrace_append hprefix tailTrace_6502556
  have hstable : (prefixWord ++ tailWord_6502556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502556).length < 2 ^ (prefixWord ++ tailWord_6502556).sum := by decide
  have hdescent : baseEnd_6502556 < baseStart_6502556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502577 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_6502577 : Nat := 118140960795 + 6502577 * 2 ^ 59
def prefixEnd_6502577 : Nat := 4983230072969 + 3 ^ 40 * 6502577 * 2
def baseEnd_6502577 : Nat := 1112982497957103457094233

theorem tailTrace_6502577 : CollatzResearch.WordTrace tailWord_6502577 prefixEnd_6502577 1112982497957103457094233 := by
  unfold tailWord_6502577
  simp only [CollatzResearch.WordTrace]
  refine ⟨237168467363281555581169985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158112311575521037054113323 237168467363281555581169985)
  ·
    refine ⟨177876350522461166685877489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237168467363281555581169985 177876350522461166685877489)
    ·
      refine ⟨133407262891845875014408117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177876350522461166685877489 133407262891845875014408117)
      ·
        refine ⟨12506930896110550782600761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133407262891845875014408117 12506930896110550782600761)
        ·
          refine ⟨9380198172082913086950571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12506930896110550782600761 9380198172082913086950571)
          ·
            refine ⟨14070297258124369630425857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380198172082913086950571 14070297258124369630425857)
            ·
              refine ⟨10552722943593277222819393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14070297258124369630425857 10552722943593277222819393)
              ·
                refine ⟨7914542207694957917114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10552722943593277222819393 7914542207694957917114545)
                ·
                  refine ⟨5935906655771218437835909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914542207694957917114545 5935906655771218437835909)
                  ·
                    refine ⟨1112982497957103457094233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935906655771218437835909 1112982497957103457094233)
                    ·
                      rfl

theorem cell23_6502577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_6502577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502577 prefixEnd_6502577 := by exact prefixLift 6502577
  have htrace : WordTrace (prefixWord ++ tailWord_6502577) baseStart_6502577 baseEnd_6502577 := by
    simpa [prefixWord, tailWord_6502577, baseEnd_6502577] using wordTrace_append hprefix tailTrace_6502577
  have hstable : (prefixWord ++ tailWord_6502577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502577).length < 2 ^ (prefixWord ++ tailWord_6502577).sum := by decide
  have hdescent : baseEnd_6502577 < baseStart_6502577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502586 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_6502586 : Nat := 118140960795 + 6502586 * 2 ^ 59
def prefixEnd_6502586 : Nat := 4983230072969 + 3 ^ 40 * 6502586 * 2
def baseEnd_6502586 : Nat := 1112984038399066945356719

theorem tailTrace_6502586 : CollatzResearch.WordTrace tailWord_6502586 prefixEnd_6502586 1112984038399066945356719 := by
  unfold tailWord_6502586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59292198905062237529561903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158112530413499300078831741 59292198905062237529561903)
  ·
    refine ⟨88938298357593356294342855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59292198905062237529561903 88938298357593356294342855)
    ·
      refine ⟨133407447536390034441514283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88938298357593356294342855 133407447536390034441514283)
      ·
        refine ⟨200111171304585051662271425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133407447536390034441514283 200111171304585051662271425)
        ·
          refine ⟨150083378478438788746703569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200111171304585051662271425 150083378478438788746703569)
          ·
            refine ⟨112562533858829091560027677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150083378478438788746703569 112562533858829091560027677)
            ·
              refine ⟨42210950197060909335010379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112562533858829091560027677 42210950197060909335010379)
              ·
                refine ⟨63316425295591364002515569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42210950197060909335010379 63316425295591364002515569)
                ·
                  refine ⟨47487318971693523001886677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63316425295591364002515569 47487318971693523001886677)
                  ·
                    refine ⟨1112984038399066945356719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47487318971693523001886677 1112984038399066945356719)
                    ·
                      rfl

theorem cell23_6502586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_6502586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502586 prefixEnd_6502586 := by exact prefixLift 6502586
  have htrace : WordTrace (prefixWord ++ tailWord_6502586) baseStart_6502586 baseEnd_6502586 := by
    simpa [prefixWord, tailWord_6502586, baseEnd_6502586] using wordTrace_append hprefix tailTrace_6502586
  have hstable : (prefixWord ++ tailWord_6502586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502586).length < 2 ^ (prefixWord ++ tailWord_6502586).sum := by decide
  have hdescent : baseEnd_6502586 < baseStart_6502586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502590 : List Nat := [4, 2, 1, 1, 4, 2, 1, 8]
def baseStart_6502590 : Nat := 118140960795 + 6502590 * 2 ^ 59
def prefixEnd_6502590 : Nat := 4983230072969 + 3 ^ 40 * 6502590 * 2
def baseEnd_6502590 : Nat := 123664969226659956311857

theorem tailTrace_6502590 : CollatzResearch.WordTrace tailWord_6502590 prefixEnd_6502590 123664969226659956311857 := by
  unfold tailWord_6502590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646117689029307350174153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158112627674822972534262149 29646117689029307350174153)
  ·
    refine ⟨22234588266771980512630615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29646117689029307350174153 22234588266771980512630615)
    ·
      refine ⟨33351882400157970768945923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22234588266771980512630615 33351882400157970768945923)
      ·
        refine ⟨50027823600236956153418885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33351882400157970768945923 50027823600236956153418885)
        ·
          refine ⟨9380216925044429278766041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50027823600236956153418885 9380216925044429278766041)
          ·
            refine ⟨7035162693783321959074531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9380216925044429278766041 7035162693783321959074531)
            ·
              refine ⟨10552744040674982938611797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035162693783321959074531 10552744040674982938611797)
              ·
                refine ⟨123664969226659956311857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10552744040674982938611797 123664969226659956311857)
                ·
                  rfl

theorem cell23_6502590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_6502590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502590 prefixEnd_6502590 := by exact prefixLift 6502590
  have htrace : WordTrace (prefixWord ++ tailWord_6502590) baseStart_6502590 baseEnd_6502590 := by
    simpa [prefixWord, tailWord_6502590, baseEnd_6502590] using wordTrace_append hprefix tailTrace_6502590
  have hstable : (prefixWord ++ tailWord_6502590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502590).length < 2 ^ (prefixWord ++ tailWord_6502590).sum := by decide
  have hdescent : baseEnd_6502590 < baseStart_6502590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502594 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6502594 : Nat := 118140960795 + 6502594 * 2 ^ 59
def prefixEnd_6502594 : Nat := 4983230072969 + 3 ^ 40 * 6502594 * 2
def baseEnd_6502594 : Nat := 1112985407680812268256707

theorem tailTrace_6502594 : CollatzResearch.WordTrace tailWord_6502594 prefixEnd_6502594 1112985407680812268256707 := by
  unfold tailWord_6502594
  simp only [CollatzResearch.WordTrace]
  refine ⟨59292271851054991871134709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158112724936146644989692557 59292271851054991871134709)
  ·
    refine ⟨5558650486036405487918879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59292271851054991871134709 5558650486036405487918879)
    ·
      refine ⟨8337975729054608231878319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558650486036405487918879 8337975729054608231878319)
      ·
        refine ⟨12506963593581912347817479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337975729054608231878319 12506963593581912347817479)
        ·
          refine ⟨18760445390372868521726219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12506963593581912347817479 18760445390372868521726219)
          ·
            refine ⟨28140668085559302782589329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18760445390372868521726219 28140668085559302782589329)
            ·
              refine ⟨21105501064169477086941997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28140668085559302782589329 21105501064169477086941997)
              ·
                refine ⟨7914562899063553907603249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21105501064169477086941997 7914562899063553907603249)
                ·
                  refine ⟨5935922174297665430702437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914562899063553907603249 5935922174297665430702437)
                  ·
                    refine ⟨1112985407680812268256707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5935922174297665430702437 1112985407680812268256707)
                    ·
                      rfl

theorem cell23_6502594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6502594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502594 prefixEnd_6502594 := by exact prefixLift 6502594
  have htrace : WordTrace (prefixWord ++ tailWord_6502594) baseStart_6502594 baseEnd_6502594 := by
    simpa [prefixWord, tailWord_6502594, baseEnd_6502594] using wordTrace_append hprefix tailTrace_6502594
  have hstable : (prefixWord ++ tailWord_6502594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502594).length < 2 ^ (prefixWord ++ tailWord_6502594).sum := by decide
  have hdescent : baseEnd_6502594 < baseStart_6502594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502708 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_6502708 : Nat := 118140960795 + 6502708 * 2 ^ 59
def prefixEnd_6502708 : Nat := 4983230072969 + 3 ^ 40 * 6502708 * 2
def baseEnd_6502708 : Nat := 3339014759837049358744597

theorem tailTrace_6502708 : CollatzResearch.WordTrace tailWord_6502708 prefixEnd_6502708 3339014759837049358744597 := by
  unfold tailWord_6502708
  simp only [CollatzResearch.WordTrace]
  refine ⟨118586622662903482477094389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158115496883871309969459185 118586622662903482477094389)
  ·
    refine ⟨11117495874647201482227599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118586622662903482477094389 11117495874647201482227599)
    ·
      refine ⟨16676243811970802223341399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11117495874647201482227599 16676243811970802223341399)
      ·
        refine ⟨25014365717956203335012099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676243811970802223341399 25014365717956203335012099)
        ·
          refine ⟨37521548576934305002518149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25014365717956203335012099 37521548576934305002518149)
          ·
            refine ⟨7035290358175182187972153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37521548576934305002518149 7035290358175182187972153)
            ·
              refine ⟨5276467768631386640979115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035290358175182187972153 5276467768631386640979115)
              ·
                refine ⟨7914701652947079961468673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276467768631386640979115 7914701652947079961468673)
                ·
                  refine ⟨5936026239710309971101505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914701652947079961468673 5936026239710309971101505)
                  ·
                    refine ⟨4452019679782732478326129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5936026239710309971101505 4452019679782732478326129)
                    ·
                      refine ⟨3339014759837049358744597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452019679782732478326129 3339014759837049358744597)
                      ·
                        rfl

theorem cell23_6502708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_6502708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502708 prefixEnd_6502708 := by exact prefixLift 6502708
  have htrace : WordTrace (prefixWord ++ tailWord_6502708) baseStart_6502708 baseEnd_6502708 := by
    simpa [prefixWord, tailWord_6502708, baseEnd_6502708] using wordTrace_append hprefix tailTrace_6502708
  have hstable : (prefixWord ++ tailWord_6502708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502708).length < 2 ^ (prefixWord ++ tailWord_6502708).sum := by decide
  have hdescent : baseEnd_6502708 < baseStart_6502708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502730 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_6502730 : Nat := 118140960795 + 6502730 * 2 ^ 59
def prefixEnd_6502730 : Nat := 4983230072969 + 3 ^ 40 * 6502730 * 2
def baseEnd_6502730 : Nat := 3339026056411448272669495

theorem tailTrace_6502730 : CollatzResearch.WordTrace tailWord_6502730 prefixEnd_6502730 3339026056411448272669495 := by
  unfold tailWord_6502730
  simp only [CollatzResearch.WordTrace]
  refine ⟨59293511932931815677872411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158116031821151508474326429 59293511932931815677872411)
  ·
    refine ⟨88940267899397723516808617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59293511932931815677872411 88940267899397723516808617)
    ·
      refine ⟨66705200924548292637606463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88940267899397723516808617 66705200924548292637606463)
      ·
        refine ⟨100057801386822438956409695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66705200924548292637606463 100057801386822438956409695)
        ·
          refine ⟨150086702080233658434614543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100057801386822438956409695 150086702080233658434614543)
          ·
            refine ⟨225130053120350487651921815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150086702080233658434614543 225130053120350487651921815)
            ·
              refine ⟨337695079680525731477882723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225130053120350487651921815 337695079680525731477882723)
              ·
                refine ⟨506542619520788597216824085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337695079680525731477882723 506542619520788597216824085)
                ·
                  refine ⟨23744185290036965494538629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 506542619520788597216824085 23744185290036965494538629)
                  ·
                    refine ⟨4452034741881931030225993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23744185290036965494538629 4452034741881931030225993)
                    ·
                      refine ⟨3339026056411448272669495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452034741881931030225993 3339026056411448272669495)
                      ·
                        rfl

theorem cell23_6502730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_6502730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502730 prefixEnd_6502730 := by exact prefixLift 6502730
  have htrace : WordTrace (prefixWord ++ tailWord_6502730) baseStart_6502730 baseEnd_6502730 := by
    simpa [prefixWord, tailWord_6502730, baseEnd_6502730] using wordTrace_append hprefix tailTrace_6502730
  have hstable : (prefixWord ++ tailWord_6502730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502730).length < 2 ^ (prefixWord ++ tailWord_6502730).sum := by decide
  have hdescent : baseEnd_6502730 < baseStart_6502730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502743 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_6502743 : Nat := 118140960795 + 6502743 * 2 ^ 59
def prefixEnd_6502743 : Nat := 4983230072969 + 3 ^ 40 * 6502743 * 2
def baseEnd_6502743 : Nat := 3339032731659956721806935

theorem tailTrace_6502743 : CollatzResearch.WordTrace tailWord_6502743 prefixEnd_6502743 3339032731659956721806935 := by
  unfold tailWord_6502743
  simp only [CollatzResearch.WordTrace]
  refine ⟨237174521880680165931712883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158116347920453443954475255 237174521880680165931712883)
  ·
    refine ⟨355761782821020248897569325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237174521880680165931712883 355761782821020248897569325)
    ·
      refine ⟨133410668557882593336588497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355761782821020248897569325 133410668557882593336588497)
      ·
        refine ⟨100058001418411945002441373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133410668557882593336588497 100058001418411945002441373)
        ·
          refine ⟨37521750531904479375915515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100058001418411945002441373 37521750531904479375915515)
          ·
            refine ⟨56282625797856719063873273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37521750531904479375915515 56282625797856719063873273)
            ·
              refine ⟨42211969348392539297904955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56282625797856719063873273 42211969348392539297904955)
              ·
                refine ⟨63317954022588808946857433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42211969348392539297904955 63317954022588808946857433)
                ·
                  refine ⟨47488465516941606710143075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63317954022588808946857433 47488465516941606710143075)
                  ·
                    refine ⟨71232698275412410065214613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47488465516941606710143075 71232698275412410065214613)
                    ·
                      refine ⟨3339032731659956721806935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71232698275412410065214613 3339032731659956721806935)
                      ·
                        rfl

theorem cell23_6502743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_6502743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502743 prefixEnd_6502743 := by exact prefixLift 6502743
  have htrace : WordTrace (prefixWord ++ tailWord_6502743) baseStart_6502743 baseEnd_6502743 := by
    simpa [prefixWord, tailWord_6502743, baseEnd_6502743] using wordTrace_append hprefix tailTrace_6502743
  have hstable : (prefixWord ++ tailWord_6502743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502743).length < 2 ^ (prefixWord ++ tailWord_6502743).sum := by decide
  have hdescent : baseEnd_6502743 < baseStart_6502743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502748 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 5]
def baseStart_6502748 : Nat := 118140960795 + 6502748 * 2 ^ 59
def prefixEnd_6502748 : Nat := 4983230072969 + 3 ^ 40 * 6502748 * 2
def baseEnd_6502748 : Nat := 371003922118136578027157

theorem tailTrace_6502748 : CollatzResearch.WordTrace tailWord_6502748 prefixEnd_6502748 371003922118136578027157 := by
  unfold tailWord_6502748
  simp only [CollatzResearch.WordTrace]
  refine ⟨118587352122831025892822449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158116469497108034523763265 118587352122831025892822449)
  ·
    refine ⟨88940514092123269419616837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118587352122831025892822449 88940514092123269419616837)
    ·
      refine ⟨16676346392273113016178157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88940514092123269419616837 16676346392273113016178157)
      ·
        refine ⟨6253629897102417381066809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16676346392273113016178157 6253629897102417381066809)
        ·
          refine ⟨4690222422826813035800107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6253629897102417381066809 4690222422826813035800107)
          ·
            refine ⟨7035333634240219553700161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690222422826813035800107 7035333634240219553700161)
            ·
              refine ⟨5276500225680164665275121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035333634240219553700161 5276500225680164665275121)
              ·
                refine ⟨3957375169260123498956341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276500225680164665275121 3957375169260123498956341)
                ·
                  refine ⟨371003922118136578027157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3957375169260123498956341 371003922118136578027157)
                  ·
                    rfl

theorem cell23_6502748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_6502748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502748 prefixEnd_6502748 := by exact prefixLift 6502748
  have htrace : WordTrace (prefixWord ++ tailWord_6502748) baseStart_6502748 baseEnd_6502748 := by
    simpa [prefixWord, tailWord_6502748, baseEnd_6502748] using wordTrace_append hprefix tailTrace_6502748
  have hstable : (prefixWord ++ tailWord_6502748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502748).length < 2 ^ (prefixWord ++ tailWord_6502748).sum := by decide
  have hdescent : baseEnd_6502748 < baseStart_6502748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502770 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_6502770 : Nat := 118140960795 + 6502770 * 2 ^ 59
def prefixEnd_6502770 : Nat := 4983230072969 + 3 ^ 40 * 6502770 * 2
def baseEnd_6502770 : Nat := 371005177293069790685479

theorem tailTrace_6502770 : CollatzResearch.WordTrace tailWord_6502770 prefixEnd_6502770 371005177293069790685479 := by
  unfold tailWord_6502770
  simp only [CollatzResearch.WordTrace]
  refine ⟨59293876662895587385736441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158117004434388233028630509 59293876662895587385736441)
  ·
    refine ⟨44470407497171690539302331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59293876662895587385736441 44470407497171690539302331)
    ·
      refine ⟨66705611245757535808953497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44470407497171690539302331 66705611245757535808953497)
      ·
        refine ⟨50029208434318151856715123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66705611245757535808953497 50029208434318151856715123)
        ·
          refine ⟨75043812651477227785072685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50029208434318151856715123 75043812651477227785072685)
          ·
            refine ⟨28141429744303960419402257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75043812651477227785072685 28141429744303960419402257)
            ·
              refine ⟨21106072308227970314551693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28141429744303960419402257 21106072308227970314551693)
              ·
                refine ⟨7914777115585488867956885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21106072308227970314551693 7914777115585488867956885)
                ·
                  refine ⟨371005177293069790685479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7914777115585488867956885 371005177293069790685479)
                  ·
                    rfl

theorem cell23_6502770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_6502770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502770 prefixEnd_6502770 := by exact prefixLift 6502770
  have htrace : WordTrace (prefixWord ++ tailWord_6502770) baseStart_6502770 baseEnd_6502770 := by
    simpa [prefixWord, tailWord_6502770, baseEnd_6502770] using wordTrace_append hprefix tailTrace_6502770
  have hstable : (prefixWord ++ tailWord_6502770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502770).length < 2 ^ (prefixWord ++ tailWord_6502770).sum := by decide
  have hdescent : baseEnd_6502770 < baseStart_6502770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502804 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 6]
def baseStart_6502804 : Nat := 118140960795 + 6502804 * 2 ^ 59
def prefixEnd_6502804 : Nat := 4983230072969 + 3 ^ 40 * 6502804 * 2
def baseEnd_6502804 : Nat := 371007117108875664793795

theorem tailTrace_6502804 : CollatzResearch.WordTrace tailWord_6502804 prefixEnd_6502804 371007117108875664793795 := by
  unfold tailWord_6502804
  simp only [CollatzResearch.WordTrace]
  refine ⟨118588373366729586674841733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158117831155639448899788977 118588373366729586674841733)
  ·
    refine ⟨22235320006261797501532825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118588373366729586674841733 22235320006261797501532825)
    ·
      refine ⟨16676490004696348126149619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22235320006261797501532825 16676490004696348126149619)
      ·
        refine ⟨25014735007044522189224429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16676490004696348126149619 25014735007044522189224429)
        ·
          refine ⟨9380525627641695820959161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25014735007044522189224429 9380525627641695820959161)
          ·
            refine ⟨7035394220731271865719371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9380525627641695820959161 7035394220731271865719371)
            ·
              refine ⟨10553091331096907798579057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035394220731271865719371 10553091331096907798579057)
              ·
                refine ⟨7914818498322680848934293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10553091331096907798579057 7914818498322680848934293)
                ·
                  refine ⟨371007117108875664793795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7914818498322680848934293 371007117108875664793795)
                  ·
                    rfl

theorem cell23_6502804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_6502804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502804 prefixEnd_6502804 := by exact prefixLift 6502804
  have htrace : WordTrace (prefixWord ++ tailWord_6502804) baseStart_6502804 baseEnd_6502804 := by
    simpa [prefixWord, tailWord_6502804, baseEnd_6502804] using wordTrace_append hprefix tailTrace_6502804
  have hstable : (prefixWord ++ tailWord_6502804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502804).length < 2 ^ (prefixWord ++ tailWord_6502804).sum := by decide
  have hdescent : baseEnd_6502804 < baseStart_6502804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502807 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_6502807 : Nat := 118140960795 + 6502807 * 2 ^ 59
def prefixEnd_6502807 : Nat := 4983230072969 + 3 ^ 40 * 6502807 * 2
def baseEnd_6502807 : Nat := 3339065594421844471406641

theorem tailTrace_6502807 : CollatzResearch.WordTrace tailWord_6502807 prefixEnd_6502807 3339065594421844471406641 := by
  unfold tailWord_6502807
  simp only [CollatzResearch.WordTrace]
  refine ⟨237176856152448304862042675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158117904101632203241361783 237176856152448304862042675)
  ·
    refine ⟨355765284228672457293064013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237176856152448304862042675 355765284228672457293064013)
    ·
      refine ⟨133411981585752171484899005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355765284228672457293064013 133411981585752171484899005)
      ·
        refine ⟨50029493094657064306837127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133411981585752171484899005 50029493094657064306837127)
        ·
          refine ⟨75044239641985596460255691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50029493094657064306837127 75044239641985596460255691)
          ·
            refine ⟨112566359462978394690383537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75044239641985596460255691 112566359462978394690383537)
            ·
              refine ⟨84424769597233796017787653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112566359462978394690383537 84424769597233796017787653)
              ·
                refine ⟨15829644299481336753335185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84424769597233796017787653 15829644299481336753335185)
                ·
                  refine ⟨11872233224611002565001389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15829644299481336753335185 11872233224611002565001389)
                  ·
                    refine ⟨4452087459229125961875521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11872233224611002565001389 4452087459229125961875521)
                    ·
                      refine ⟨3339065594421844471406641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452087459229125961875521 3339065594421844471406641)
                      ·
                        rfl

theorem cell23_6502807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_6502807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502807 prefixEnd_6502807 := by exact prefixLift 6502807
  have htrace : WordTrace (prefixWord ++ tailWord_6502807) baseStart_6502807 baseEnd_6502807 := by
    simpa [prefixWord, tailWord_6502807, baseEnd_6502807] using wordTrace_append hprefix tailTrace_6502807
  have hstable : (prefixWord ++ tailWord_6502807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502807).length < 2 ^ (prefixWord ++ tailWord_6502807).sum := by decide
  have hdescent : baseEnd_6502807 < baseStart_6502807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502820 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_6502820 : Nat := 118140960795 + 6502820 * 2 ^ 59
def prefixEnd_6502820 : Nat := 4983230072969 + 3 ^ 40 * 6502820 * 2
def baseEnd_6502820 : Nat := 3339072269670352920544081

theorem tailTrace_6502820 : CollatzResearch.WordTrace tailWord_6502820 prefixEnd_6502820 3339072269670352920544081 := by
  unfold tailWord_6502820
  simp only [CollatzResearch.WordTrace]
  refine ⟨118588665150700604041132957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158118220200934138721510609 118588665150700604041132957)
  ·
    refine ⟨44470749431512726515424859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118588665150700604041132957 44470749431512726515424859)
    ·
      refine ⟨66706124147269089773137289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44470749431512726515424859 66706124147269089773137289)
      ·
        refine ⟨50029593110451817329852967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66706124147269089773137289 50029593110451817329852967)
        ·
          refine ⟨75044389665677725994779451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50029593110451817329852967 75044389665677725994779451)
          ·
            refine ⟨112566584498516588992169177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75044389665677725994779451 112566584498516588992169177)
            ·
              refine ⟨84424938373887441744126883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112566584498516588992169177 84424938373887441744126883)
              ·
                refine ⟨126637407560831162616190325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84424938373887441744126883 126637407560831162616190325)
                ·
                  refine ⟨11872256958827921495267843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126637407560831162616190325 11872256958827921495267843)
                  ·
                    refine ⟨17808385438241882242901765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11872256958827921495267843 17808385438241882242901765)
                    ·
                      refine ⟨3339072269670352920544081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17808385438241882242901765 3339072269670352920544081)
                      ·
                        rfl

theorem cell23_6502820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_6502820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502820 prefixEnd_6502820 := by exact prefixLift 6502820
  have htrace : WordTrace (prefixWord ++ tailWord_6502820) baseStart_6502820 baseEnd_6502820 := by
    simpa [prefixWord, tailWord_6502820, baseEnd_6502820] using wordTrace_append hprefix tailTrace_6502820
  have hstable : (prefixWord ++ tailWord_6502820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502820).length < 2 ^ (prefixWord ++ tailWord_6502820).sum := by decide
  have hdescent : baseEnd_6502820 < baseStart_6502820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502824 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6502824 : Nat := 118140960795 + 6502824 * 2 ^ 59
def prefixEnd_6502824 : Nat := 4983230072969 + 3 ^ 40 * 6502824 * 2
def baseEnd_6502824 : Nat := 3339074323592970904894063

theorem tailTrace_6502824 : CollatzResearch.WordTrace tailWord_6502824 prefixEnd_6502824 3339074323592970904894063 := by
  unfold tailWord_6502824
  simp only [CollatzResearch.WordTrace]
  refine ⟨118588738096693358382705763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158118317462257811176941017 118588738096693358382705763)
  ·
    refine ⟨177883107145040037574058645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118588738096693358382705763 177883107145040037574058645)
    ·
      refine ⟨8338270647423751761283999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177883107145040037574058645 8338270647423751761283999)
      ·
        refine ⟨12507405971135627641925999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8338270647423751761283999 12507405971135627641925999)
        ·
          refine ⟨18761108956703441462888999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12507405971135627641925999 18761108956703441462888999)
          ·
            refine ⟨28141663435055162194333499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18761108956703441462888999 28141663435055162194333499)
            ·
              refine ⟨42212495152582743291500249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28141663435055162194333499 42212495152582743291500249)
              ·
                refine ⟨31659371364437057468625187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42212495152582743291500249 31659371364437057468625187)
                ·
                  refine ⟨47489057046655586202937781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31659371364437057468625187 47489057046655586202937781)
                  ·
                    refine ⟨4452099098123961206525417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47489057046655586202937781 4452099098123961206525417)
                    ·
                      refine ⟨3339074323592970904894063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452099098123961206525417 3339074323592970904894063)
                      ·
                        rfl

theorem cell23_6502824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6502824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502824 prefixEnd_6502824 := by exact prefixLift 6502824
  have htrace : WordTrace (prefixWord ++ tailWord_6502824) baseStart_6502824 baseEnd_6502824 := by
    simpa [prefixWord, tailWord_6502824, baseEnd_6502824] using wordTrace_append hprefix tailTrace_6502824
  have hstable : (prefixWord ++ tailWord_6502824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502824).length < 2 ^ (prefixWord ++ tailWord_6502824).sum := by decide
  have hdescent : baseEnd_6502824 < baseStart_6502824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502857 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_6502857 : Nat := 118140960795 + 6502857 * 2 ^ 59
def prefixEnd_6502857 : Nat := 4983230072969 + 3 ^ 40 * 6502857 * 2
def baseEnd_6502857 : Nat := 3339091268454569275781411

theorem tailTrace_6502857 : CollatzResearch.WordTrace tailWord_6502857 prefixEnd_6502857 3339091268454569275781411 := by
  unfold tailWord_6502857
  simp only [CollatzResearch.WordTrace]
  refine ⟨237178679802267163401362825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158119119868178108934241883 237178679802267163401362825)
  ·
    refine ⟨177884009851700372551022119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237178679802267163401362825 177884009851700372551022119)
    ·
      refine ⟨266826014777550558826533179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177884009851700372551022119 266826014777550558826533179)
      ·
        refine ⟨400239022166325838239799769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266826014777550558826533179 400239022166325838239799769)
        ·
          refine ⟨300179266624744378679849827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400239022166325838239799769 300179266624744378679849827)
          ·
            refine ⟨450268899937116568019774741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300179266624744378679849827 450268899937116568019774741)
            ·
              refine ⟨21106354684552339125926941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 450268899937116568019774741 21106354684552339125926941)
              ·
                refine ⟨7914883006707127172222603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21106354684552339125926941 7914883006707127172222603)
                ·
                  refine ⟨11872324510060690758333905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7914883006707127172222603 11872324510060690758333905)
                  ·
                    refine ⟨8904243382545518068750429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11872324510060690758333905 8904243382545518068750429)
                    ·
                      refine ⟨3339091268454569275781411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8904243382545518068750429 3339091268454569275781411)
                      ·
                        rfl

theorem cell23_6502857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_6502857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502857 prefixEnd_6502857 := by exact prefixLift 6502857
  have htrace : WordTrace (prefixWord ++ tailWord_6502857) baseStart_6502857 baseEnd_6502857 := by
    simpa [prefixWord, tailWord_6502857, baseEnd_6502857] using wordTrace_append hprefix tailTrace_6502857
  have hstable : (prefixWord ++ tailWord_6502857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502857).length < 2 ^ (prefixWord ++ tailWord_6502857).sum := by decide
  have hdescent : baseEnd_6502857 < baseStart_6502857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502887 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6502887 : Nat := 118140960795 + 6502887 * 2 ^ 59
def prefixEnd_6502887 : Nat := 4983230072969 + 3 ^ 40 * 6502887 * 2
def baseEnd_6502887 : Nat := 3339106672874204158406273

theorem tailTrace_6502887 : CollatzResearch.WordTrace tailWord_6502887 prefixEnd_6502887 3339106672874204158406273 := by
  unfold tailWord_6502887
  simp only [CollatzResearch.WordTrace]
  refine ⟨237179773992158478524954915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158119849328105652349969943 237179773992158478524954915)
  ·
    refine ⟨355769660988237717787432373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237179773992158478524954915 355769660988237717787432373)
    ·
      refine ⟨33353405717647286042571785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355769660988237717787432373 33353405717647286042571785)
      ·
        refine ⟨25015054288235464531928839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33353405717647286042571785 25015054288235464531928839)
        ·
          refine ⟨37522581432353196797893259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25015054288235464531928839 37522581432353196797893259)
          ·
            refine ⟨56283872148529795196839889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37522581432353196797893259 56283872148529795196839889)
            ·
              refine ⟨42212904111397346397629917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56283872148529795196839889 42212904111397346397629917)
              ·
                refine ⟨15829839041774004899111219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42212904111397346397629917 15829839041774004899111219)
                ·
                  refine ⟨23744758562661007348666829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15829839041774004899111219 23744758562661007348666829)
                  ·
                    refine ⟨8904284460997877755750061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23744758562661007348666829 8904284460997877755750061)
                    ·
                      refine ⟨3339106672874204158406273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8904284460997877755750061 3339106672874204158406273)
                      ·
                        rfl

theorem cell23_6502887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6502887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502887 prefixEnd_6502887 := by exact prefixLift 6502887
  have htrace : WordTrace (prefixWord ++ tailWord_6502887) baseStart_6502887 baseEnd_6502887 := by
    simpa [prefixWord, tailWord_6502887, baseEnd_6502887] using wordTrace_append hprefix tailTrace_6502887
  have hstable : (prefixWord ++ tailWord_6502887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502887).length < 2 ^ (prefixWord ++ tailWord_6502887).sum := by decide
  have hdescent : baseEnd_6502887 < baseStart_6502887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502920 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_6502920 : Nat := 118140960795 + 6502920 * 2 ^ 59
def prefixEnd_6502920 : Nat := 4983230072969 + 3 ^ 40 * 6502920 * 2
def baseEnd_6502920 : Nat := 1113041205911934176431207

theorem tailTrace_6502920 : CollatzResearch.WordTrace tailWord_6502920 prefixEnd_6502920 1113041205911934176431207 := by
  unfold tailWord_6502920
  simp only [CollatzResearch.WordTrace]
  refine ⟨118590488800519462580453107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158120651734025950107270809 118590488800519462580453107)
  ·
    refine ⟨177885733200779193870679661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118590488800519462580453107 177885733200779193870679661)
    ·
      refine ⟨66707149950292197701504873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177885733200779193870679661 66707149950292197701504873)
      ·
        refine ⟨50030362462719148276128655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66707149950292197701504873 50030362462719148276128655)
        ·
          refine ⟨75045543694078722414192983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50030362462719148276128655 75045543694078722414192983)
          ·
            refine ⟨112568315541118083621289475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75045543694078722414192983 112568315541118083621289475)
            ·
              refine ⟨168852473311677125431934213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112568315541118083621289475 168852473311677125431934213)
              ·
                refine ⟨31659838745939461018487665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168852473311677125431934213 31659838745939461018487665)
                ·
                  refine ⟨23744879059454595763865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31659838745939461018487665 23744879059454595763865749)
                  ·
                    refine ⟨1113041205911934176431207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23744879059454595763865749 1113041205911934176431207)
                    ·
                      rfl

theorem cell23_6502920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_6502920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502920 prefixEnd_6502920 := by exact prefixLift 6502920
  have htrace : WordTrace (prefixWord ++ tailWord_6502920) baseStart_6502920 baseEnd_6502920 := by
    simpa [prefixWord, tailWord_6502920, baseEnd_6502920] using wordTrace_append hprefix tailTrace_6502920
  have hstable : (prefixWord ++ tailWord_6502920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502920).length < 2 ^ (prefixWord ++ tailWord_6502920).sum := by decide
  have hdescent : baseEnd_6502920 < baseStart_6502920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6502987 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 7, 2]
def baseStart_6502987 : Nat := 118140960795 + 6502987 * 2 ^ 59
def prefixEnd_6502987 : Nat := 4983230072969 + 3 ^ 40 * 6502987 * 2
def baseEnd_6502987 : Nat := 3339158020939653767155813

theorem tailTrace_6502987 : CollatzResearch.WordTrace tailWord_6502987 prefixEnd_6502987 3339158020939653767155813 := by
  unfold tailWord_6502987
  simp only [CollatzResearch.WordTrace]
  refine ⟨237183421291796195603595215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158122280861197463735730143 237183421291796195603595215)
  ·
    refine ⟨355775131937694293405392823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237183421291796195603595215 355775131937694293405392823)
    ·
      refine ⟨533662697906541440108089235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355775131937694293405392823 533662697906541440108089235)
      ·
        refine ⟨800494046859812160162133853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533662697906541440108089235 800494046859812160162133853)
        ·
          refine ⟨300185267572429560060800195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800494046859812160162133853 300185267572429560060800195)
          ·
            refine ⟨450277901358644340091200293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300185267572429560060800195 450277901358644340091200293)
            ·
              refine ⟨84427106504745813767100055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450277901358644340091200293 84427106504745813767100055)
              ·
                refine ⟨126640659757118720650650083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84427106504745813767100055 126640659757118720650650083)
                ·
                  refine ⟨189960989635678080975975125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126640659757118720650650083 189960989635678080975975125)
                  ·
                    refine ⟨4452210694586205022874417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189960989635678080975975125 4452210694586205022874417)
                    ·
                      refine ⟨3339158020939653767155813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452210694586205022874417 3339158020939653767155813)
                      ·
                        rfl

theorem cell23_6502987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7, 2].length) (baseStart_6502987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6502987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6502987 prefixEnd_6502987 := by exact prefixLift 6502987
  have htrace : WordTrace (prefixWord ++ tailWord_6502987) baseStart_6502987 baseEnd_6502987 := by
    simpa [prefixWord, tailWord_6502987, baseEnd_6502987] using wordTrace_append hprefix tailTrace_6502987
  have hstable : (prefixWord ++ tailWord_6502987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6502987).length < 2 ^ (prefixWord ++ tailWord_6502987).sum := by decide
  have hdescent : baseEnd_6502987 < baseStart_6502987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6502987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503017 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_6503017 : Nat := 118140960795 + 6503017 * 2 ^ 59
def prefixEnd_6503017 : Nat := 4983230072969 + 3 ^ 40 * 6503017 * 2
def baseEnd_6503017 : Nat := 3339173425359288649780675

theorem tailTrace_6503017 : CollatzResearch.WordTrace tailWord_6503017 prefixEnd_6503017 3339173425359288649780675 := by
  unfold tailWord_6503017
  simp only [CollatzResearch.WordTrace]
  refine ⟨237184515481687510727187305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158123010321125007151458203 237184515481687510727187305)
  ·
    refine ⟨177888386611265633045390479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237184515481687510727187305 177888386611265633045390479)
    ·
      refine ⟨266832579916898449568085719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177888386611265633045390479 266832579916898449568085719)
      ·
        refine ⟨400248869875347674352128579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266832579916898449568085719 400248869875347674352128579)
        ·
          refine ⟨600373304813021511528192869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400248869875347674352128579 600373304813021511528192869)
          ·
            refine ⟨112569994652441533411536163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 600373304813021511528192869 112569994652441533411536163)
            ·
              refine ⟨168854991978662300117304245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112569994652441533411536163 168854991978662300117304245)
              ·
                refine ⟨15830155497999590635997273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168854991978662300117304245 15830155497999590635997273)
                ·
                  refine ⟨11872616623499692976997955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15830155497999590635997273 11872616623499692976997955)
                  ·
                    refine ⟨17808924935249539465496933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11872616623499692976997955 17808924935249539465496933)
                    ·
                      refine ⟨3339173425359288649780675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17808924935249539465496933 3339173425359288649780675)
                      ·
                        rfl

theorem cell23_6503017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_6503017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503017 prefixEnd_6503017 := by exact prefixLift 6503017
  have htrace : WordTrace (prefixWord ++ tailWord_6503017) baseStart_6503017 baseEnd_6503017 := by
    simpa [prefixWord, tailWord_6503017, baseEnd_6503017] using wordTrace_append hprefix tailTrace_6503017
  have hstable : (prefixWord ++ tailWord_6503017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503017).length < 2 ^ (prefixWord ++ tailWord_6503017).sum := by decide
  have hdescent : baseEnd_6503017 < baseStart_6503017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503054 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_6503054 : Nat := 118140960795 + 6503054 * 2 ^ 59
def prefixEnd_6503054 : Nat := 4983230072969 + 3 ^ 40 * 6503054 * 2
def baseEnd_6503054 : Nat := 3339192424143505005018005

theorem tailTrace_6503054 : CollatzResearch.WordTrace tailWord_6503054 prefixEnd_6503054 3339192424143505005018005 := by
  unfold tailWord_6503054
  simp only [CollatzResearch.WordTrace]
  refine ⟨29648233122819183255785527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158123909988368977364189477 29648233122819183255785527)
  ·
    refine ⟨44472349684228774883678291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29648233122819183255785527 44472349684228774883678291)
    ·
      refine ⟨66708524526343162325517437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44472349684228774883678291 66708524526343162325517437)
      ·
        refine ⟨25015696697378685872069039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66708524526343162325517437 25015696697378685872069039)
        ·
          refine ⟨37523545046068028808103559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25015696697378685872069039 37523545046068028808103559)
          ·
            refine ⟨56285317569102043212155339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37523545046068028808103559 56285317569102043212155339)
            ·
              refine ⟨84427976353653064818233009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56285317569102043212155339 84427976353653064818233009)
              ·
                refine ⟨63320982265239798613674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84427976353653064818233009 63320982265239798613674757)
                ·
                  refine ⟨11872684174732462240064017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63320982265239798613674757 11872684174732462240064017)
                  ·
                    refine ⟨8904513131049346680048013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11872684174732462240064017 8904513131049346680048013)
                    ·
                      refine ⟨3339192424143505005018005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8904513131049346680048013 3339192424143505005018005)
                      ·
                        rfl

theorem cell23_6503054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_6503054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503054 prefixEnd_6503054 := by exact prefixLift 6503054
  have htrace : WordTrace (prefixWord ++ tailWord_6503054) baseStart_6503054 baseEnd_6503054 := by
    simpa [prefixWord, tailWord_6503054, baseEnd_6503054] using wordTrace_append hprefix tailTrace_6503054
  have hstable : (prefixWord ++ tailWord_6503054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503054).length < 2 ^ (prefixWord ++ tailWord_6503054).sum := by decide
  have hdescent : baseEnd_6503054 < baseStart_6503054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503095 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 1, 4]
def baseStart_6503095 : Nat := 118140960795 + 6503095 * 2 ^ 59
def prefixEnd_6503095 : Nat := 4983230072969 + 3 ^ 40 * 6503095 * 2
def baseEnd_6503095 : Nat := 1113071158950113114868439

theorem tailTrace_6503095 : CollatzResearch.WordTrace tailWord_6503095 prefixEnd_6503095 1113071158950113114868439 := by
  unfold tailWord_6503095
  simp only [CollatzResearch.WordTrace]
  refine ⟨237187360375404930048526739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158124906916936620032351159 237187360375404930048526739)
  ·
    refine ⟨355781040563107395072790109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237187360375404930048526739 355781040563107395072790109)
    ·
      refine ⟨133417890211165273152296291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355781040563107395072790109 133417890211165273152296291)
      ·
        refine ⟨200126835316747909728444437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133417890211165273152296291 200126835316747909728444437)
        ·
          refine ⟨9380945405472558268520833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200126835316747909728444437 9380945405472558268520833)
          ·
            refine ⟨7035709054104418701390625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9380945405472558268520833 7035709054104418701390625)
            ·
              refine ⟨5276781790578314026042969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035709054104418701390625 5276781790578314026042969)
              ·
                refine ⟨3957586342933735519532227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276781790578314026042969 3957586342933735519532227)
                ·
                  refine ⟨5936379514400603279298341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957586342933735519532227 5936379514400603279298341)
                  ·
                    refine ⟨1113071158950113114868439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936379514400603279298341 1113071158950113114868439)
                    ·
                      rfl

theorem cell23_6503095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_6503095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503095 prefixEnd_6503095 := by exact prefixLift 6503095
  have htrace : WordTrace (prefixWord ++ tailWord_6503095) baseStart_6503095 baseEnd_6503095 := by
    simpa [prefixWord, tailWord_6503095, baseEnd_6503095] using wordTrace_append hprefix tailTrace_6503095
  have hstable : (prefixWord ++ tailWord_6503095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503095).length < 2 ^ (prefixWord ++ tailWord_6503095).sum := by decide
  have hdescent : baseEnd_6503095 < baseStart_6503095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503128 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_6503128 : Nat := 118140960795 + 6503128 * 2 ^ 59
def prefixEnd_6503128 : Nat := 4983230072969 + 3 ^ 40 * 6503128 * 2
def baseEnd_6503128 : Nat := 3339230421711937715492665

theorem tailTrace_6503128 : CollatzResearch.WordTrace tailWord_6503128 prefixEnd_6503128 3339230421711937715492665 := by
  unfold tailWord_6503128
  simp only [CollatzResearch.WordTrace]
  refine ⟨118594281992142688342239019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158125709322856917789652025 118594281992142688342239019)
  ·
    refine ⟨177891422988214032513358529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118594281992142688342239019 177891422988214032513358529)
    ·
      refine ⟨133418567241160524385018897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177891422988214032513358529 133418567241160524385018897)
      ·
        refine ⟨100063925430870393288764173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133418567241160524385018897 100063925430870393288764173)
        ·
          refine ⟨37523972036576397483286565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100063925430870393288764173 37523972036576397483286565)
          ·
            refine ⟨7035744756858074528116231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37523972036576397483286565 7035744756858074528116231)
            ·
              refine ⟨10553617135287111792174347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7035744756858074528116231 10553617135287111792174347)
              ·
                refine ⟨15830425702930667688261521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553617135287111792174347 15830425702930667688261521)
                ·
                  refine ⟨11872819277198000766196141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15830425702930667688261521 11872819277198000766196141)
                  ·
                    refine ⟨4452307228949250287323553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11872819277198000766196141 4452307228949250287323553)
                    ·
                      refine ⟨3339230421711937715492665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452307228949250287323553 3339230421711937715492665)
                      ·
                        rfl

theorem cell23_6503128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_6503128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503128 prefixEnd_6503128 := by exact prefixLift 6503128
  have htrace : WordTrace (prefixWord ++ tailWord_6503128) baseStart_6503128 baseEnd_6503128 := by
    simpa [prefixWord, tailWord_6503128, baseEnd_6503128] using wordTrace_append hprefix tailTrace_6503128
  have hstable : (prefixWord ++ tailWord_6503128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503128).length < 2 ^ (prefixWord ++ tailWord_6503128).sum := by decide
  have hdescent : baseEnd_6503128 < baseStart_6503128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503141 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6503141 : Nat := 118140960795 + 6503141 * 2 ^ 59
def prefixEnd_6503141 : Nat := 4983230072969 + 3 ^ 40 * 6503141 * 2
def baseEnd_6503141 : Nat := 3339237096960446164630105

theorem tailTrace_6503141 : CollatzResearch.WordTrace tailWord_6503141 prefixEnd_6503141 3339237096960446164630105 := by
  unfold tailWord_6503141
  simp only [CollatzResearch.WordTrace]
  refine ⟨237189038133238279904701277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158126025422158853269800851 237189038133238279904701277)
  ·
    refine ⟨88945889299964354964262979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237189038133238279904701277 88945889299964354964262979)
    ·
      refine ⟨133418833949946532446394469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88945889299964354964262979 133418833949946532446394469)
      ·
        refine ⟨25016031365614974833698963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133418833949946532446394469 25016031365614974833698963)
        ·
          refine ⟨37524047048422462250548445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25016031365614974833698963 37524047048422462250548445)
          ·
            refine ⟨14071517643158423343955667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37524047048422462250548445 14071517643158423343955667)
            ·
              refine ⟨21107276464737635015933501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14071517643158423343955667 21107276464737635015933501)
              ·
                refine ⟨7915228674276613130975063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21107276464737635015933501 7915228674276613130975063)
                ·
                  refine ⟨11872843011414919696462595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7915228674276613130975063 11872843011414919696462595)
                  ·
                    refine ⟨17809264517122379544693893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11872843011414919696462595 17809264517122379544693893)
                    ·
                      refine ⟨3339237096960446164630105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17809264517122379544693893 3339237096960446164630105)
                      ·
                        rfl

theorem cell23_6503141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6503141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503141 prefixEnd_6503141 := by exact prefixLift 6503141
  have htrace : WordTrace (prefixWord ++ tailWord_6503141) baseStart_6503141 baseEnd_6503141 := by
    simpa [prefixWord, tailWord_6503141, baseEnd_6503141] using wordTrace_append hprefix tailTrace_6503141
  have hstable : (prefixWord ++ tailWord_6503141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503141).length < 2 ^ (prefixWord ++ tailWord_6503141).sum := by decide
  have hdescent : baseEnd_6503141 < baseStart_6503141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503151 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 2, 4]
def baseStart_6503151 : Nat := 118140960795 + 6503151 * 2 ^ 59
def prefixEnd_6503151 : Nat := 4983230072969 + 3 ^ 40 * 6503151 * 2
def baseEnd_6503151 : Nat := 1113080743922330375168353

theorem tailTrace_6503151 : CollatzResearch.WordTrace tailWord_6503151 prefixEnd_6503151 1113080743922330375168353 := by
  unfold tailWord_6503151
  simp only [CollatzResearch.WordTrace]
  refine ⟨237189402863202051612565307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158126268575468034408376871 237189402863202051612565307)
  ·
    refine ⟨355784104294803077418847961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237189402863202051612565307 355784104294803077418847961)
    ·
      refine ⟨266838078221102308064135971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355784104294803077418847961 266838078221102308064135971)
      ·
        refine ⟨400257117331653462096203957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266838078221102308064135971 400257117331653462096203957)
        ·
          refine ⟨37524104749842512071519121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400257117331653462096203957 37524104749842512071519121)
          ·
            refine ⟨28143078562381884053639341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37524104749842512071519121 28143078562381884053639341)
            ·
              refine ⟨10553654460893206520114753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28143078562381884053639341 10553654460893206520114753)
              ·
                refine ⟨7915240845669904890086065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10553654460893206520114753 7915240845669904890086065)
                ·
                  refine ⟨5936430634252428667564549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7915240845669904890086065 5936430634252428667564549)
                  ·
                    refine ⟨1113080743922330375168353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936430634252428667564549 1113080743922330375168353)
                    ·
                      rfl

theorem cell23_6503151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_6503151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503151 prefixEnd_6503151 := by exact prefixLift 6503151
  have htrace : WordTrace (prefixWord ++ tailWord_6503151) baseStart_6503151 baseEnd_6503151 := by
    simpa [prefixWord, tailWord_6503151, baseEnd_6503151] using wordTrace_append hprefix tailTrace_6503151
  have hstable : (prefixWord ++ tailWord_6503151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503151).length < 2 ^ (prefixWord ++ tailWord_6503151).sum := by decide
  have hdescent : baseEnd_6503151 < baseStart_6503151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503177 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_6503177 : Nat := 118140960795 + 6503177 * 2 ^ 59
def prefixEnd_6503177 : Nat := 4983230072969 + 3 ^ 40 * 6503177 * 2
def baseEnd_6503177 : Nat := 1113085194088002674593313

theorem tailTrace_6503177 : CollatzResearch.WordTrace tailWord_6503177 prefixEnd_6503177 1113085194088002674593313 := by
  unfold tailWord_6503177
  simp only [CollatzResearch.WordTrace]
  refine ⟨237190351161107858053011785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158126900774071905368674523 237190351161107858053011785)
  ·
    refine ⟨177892763370830893539758839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237190351161107858053011785 177892763370830893539758839)
    ·
      refine ⟨266839145056246340309638259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177892763370830893539758839 266839145056246340309638259)
      ·
        refine ⟨400258717584369510464457389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266839145056246340309638259 400258717584369510464457389)
        ·
          refine ⟨150097019094138566424171521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400258717584369510464457389 150097019094138566424171521)
          ·
            refine ⟨112572764320603924818128641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150097019094138566424171521 112572764320603924818128641)
            ·
              refine ⟨84429573240452943613596481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112572764320603924818128641 84429573240452943613596481)
              ·
                refine ⟨63322179930339707710197361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84429573240452943613596481 63322179930339707710197361)
                ·
                  refine ⟨47491634947754780782648021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63322179930339707710197361 47491634947754780782648021)
                  ·
                    refine ⟨1113085194088002674593313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47491634947754780782648021 1113085194088002674593313)
                    ·
                      rfl

theorem cell23_6503177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_6503177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503177 prefixEnd_6503177 := by exact prefixLift 6503177
  have htrace : WordTrace (prefixWord ++ tailWord_6503177) baseStart_6503177 baseEnd_6503177 := by
    simpa [prefixWord, tailWord_6503177, baseEnd_6503177] using wordTrace_append hprefix tailTrace_6503177
  have hstable : (prefixWord ++ tailWord_6503177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503177).length < 2 ^ (prefixWord ++ tailWord_6503177).sum := by decide
  have hdescent : baseEnd_6503177 < baseStart_6503177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503187 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_6503187 : Nat := 118140960795 + 6503187 * 2 ^ 59
def prefixEnd_6503187 : Nat := 4983230072969 + 3 ^ 40 * 6503187 * 2
def baseEnd_6503187 : Nat := 3339260717070552984654893

theorem tailTrace_6503187 : CollatzResearch.WordTrace tailWord_6503187 prefixEnd_6503187 3339260717070552984654893 := by
  unfold tailWord_6503187
  simp only [CollatzResearch.WordTrace]
  refine ⟨237190715891071629760875815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158127143927381086507250543 237190715891071629760875815)
  ·
    refine ⟨355786073836607444641313723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237190715891071629760875815 355786073836607444641313723)
    ·
      refine ⟨533679110754911166961970585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355786073836607444641313723 533679110754911166961970585)
      ·
        refine ⟨400259333066183375221477939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533679110754911166961970585 400259333066183375221477939)
        ·
          refine ⟨600388999599275062832216909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400259333066183375221477939 600388999599275062832216909)
          ·
            refine ⟨225145874849728148562081341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600388999599275062832216909 225145874849728148562081341)
            ·
              refine ⟨84429703068648055710780503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225145874849728148562081341 84429703068648055710780503)
              ·
                refine ⟨126644554602972083566170755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84429703068648055710780503 126644554602972083566170755)
                ·
                  refine ⟨189966831904458125349256133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126644554602972083566170755 189966831904458125349256133)
                  ·
                    refine ⟨35618780982085898502985525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189966831904458125349256133 35618780982085898502985525)
                    ·
                      refine ⟨3339260717070552984654893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35618780982085898502985525 3339260717070552984654893)
                      ·
                        rfl

theorem cell23_6503187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_6503187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503187 prefixEnd_6503187 := by exact prefixLift 6503187
  have htrace : WordTrace (prefixWord ++ tailWord_6503187) baseStart_6503187 baseEnd_6503187 := by
    simpa [prefixWord, tailWord_6503187, baseEnd_6503187] using wordTrace_append hprefix tailTrace_6503187
  have hstable : (prefixWord ++ tailWord_6503187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503187).length < 2 ^ (prefixWord ++ tailWord_6503187).sum := by decide
  have hdescent : baseEnd_6503187 < baseStart_6503187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503208 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6503208 : Nat := 118140960795 + 6503208 * 2 ^ 59
def prefixEnd_6503208 : Nat := 4983230072969 + 3 ^ 40 * 6503208 * 2
def baseEnd_6503208 : Nat := 3339271500164297402492297

theorem tailTrace_6503208 : CollatzResearch.WordTrace tailWord_6503208 prefixEnd_6503208 3339271500164297402492297 := by
  unfold tailWord_6503208
  simp only [CollatzResearch.WordTrace]
  refine ⟨118595740911997775173695139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158127654549330366898260185 118595740911997775173695139)
  ·
    refine ⟨177893611367996662760542709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118595740911997775173695139 177893611367996662760542709)
    ·
      refine ⟨16677526065749687133800879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177893611367996662760542709 16677526065749687133800879)
      ·
        refine ⟨25016289098624530700701319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16677526065749687133800879 25016289098624530700701319)
        ·
          refine ⟨37524433647936796051051979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25016289098624530700701319 37524433647936796051051979)
          ·
            refine ⟨56286650471905194076577969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37524433647936796051051979 56286650471905194076577969)
            ·
              refine ⟨42214987853928895557433477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56286650471905194076577969 42214987853928895557433477)
              ·
                refine ⟨7915310222611667917018777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42214987853928895557433477 7915310222611667917018777)
                ·
                  refine ⟨5936482666958750937764083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7915310222611667917018777 5936482666958750937764083)
                  ·
                    refine ⟨8904724000438126406646125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5936482666958750937764083 8904724000438126406646125)
                    ·
                      refine ⟨3339271500164297402492297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8904724000438126406646125 3339271500164297402492297)
                      ·
                        rfl

theorem cell23_6503208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6503208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503208 prefixEnd_6503208 := by exact prefixLift 6503208
  have htrace : WordTrace (prefixWord ++ tailWord_6503208) baseStart_6503208 baseEnd_6503208 := by
    simpa [prefixWord, tailWord_6503208, baseEnd_6503208] using wordTrace_append hprefix tailTrace_6503208
  have hstable : (prefixWord ++ tailWord_6503208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503208).length < 2 ^ (prefixWord ++ tailWord_6503208).sum := by decide
  have hdescent : baseEnd_6503208 < baseStart_6503208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503252 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_6503252 : Nat := 118140960795 + 6503252 * 2 ^ 59
def prefixEnd_6503252 : Nat := 4983230072969 + 3 ^ 40 * 6503252 * 2
def baseEnd_6503252 : Nat := 3339294093313095230342095

theorem tailTrace_6503252 : CollatzResearch.WordTrace tailWord_6503252 prefixEnd_6503252 3339294093313095230342095 := by
  unfold tailWord_6503252
  simp only [CollatzResearch.WordTrace]
  refine ⟨118596543317918072930996005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158128724423890763907994673 118596543317918072930996005)
  ·
    refine ⟨22236851872109638674561751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118596543317918072930996005 22236851872109638674561751)
    ·
      refine ⟨33355277808164458011842627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22236851872109638674561751 33355277808164458011842627)
      ·
        refine ⟨50032916712246687017763941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33355277808164458011842627 50032916712246687017763941)
        ·
          refine ⟨9381171883546253815830739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50032916712246687017763941 9381171883546253815830739)
          ·
            refine ⟨14071757825319380723746109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381171883546253815830739 14071757825319380723746109)
            ·
              refine ⟨5276909184494767771404791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14071757825319380723746109 5276909184494767771404791)
              ·
                refine ⟨7915363776742151657107187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276909184494767771404791 7915363776742151657107187)
                ·
                  refine ⟨11873045665113227485660781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7915363776742151657107187 11873045665113227485660781)
                  ·
                    refine ⟨4452392124417460307122793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11873045665113227485660781 4452392124417460307122793)
                    ·
                      refine ⟨3339294093313095230342095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452392124417460307122793 3339294093313095230342095)
                      ·
                        rfl

theorem cell23_6503252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_6503252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503252 prefixEnd_6503252 := by exact prefixLift 6503252
  have htrace : WordTrace (prefixWord ++ tailWord_6503252) baseStart_6503252 baseEnd_6503252 := by
    simpa [prefixWord, tailWord_6503252, baseEnd_6503252] using wordTrace_append hprefix tailTrace_6503252
  have hstable : (prefixWord ++ tailWord_6503252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503252).length < 2 ^ (prefixWord ++ tailWord_6503252).sum := by decide
  have hdescent : baseEnd_6503252 < baseStart_6503252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503278 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_6503278 : Nat := 118140960795 + 6503278 * 2 ^ 59
def prefixEnd_6503278 : Nat := 4983230072969 + 3 ^ 40 * 6503278 * 2
def baseEnd_6503278 : Nat := 3339307443810112128616975

theorem tailTrace_6503278 : CollatzResearch.WordTrace tailWord_6503278 prefixEnd_6503278 3339307443810112128616975 := by
  unfold tailWord_6503278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649254366717744037804811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158129356622494634868292325 29649254366717744037804811)
  ·
    refine ⟨44473881550076616056707217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29649254366717744037804811 44473881550076616056707217)
    ·
      refine ⟨33355411162557462042530413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44473881550076616056707217 33355411162557462042530413)
      ·
        refine ⟨12508279185959048265948905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33355411162557462042530413 12508279185959048265948905)
        ·
          refine ⟨9381209389469286199461679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12508279185959048265948905 9381209389469286199461679)
          ·
            refine ⟨14071814084203929299192519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381209389469286199461679 14071814084203929299192519)
            ·
              refine ⟨21107721126305893948788779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14071814084203929299192519 21107721126305893948788779)
              ·
                refine ⟨31661581689458840923183169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21107721126305893948788779 31661581689458840923183169)
                ·
                  refine ⟨23746186267094130692387377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31661581689458840923183169 23746186267094130692387377)
                  ·
                    refine ⟨17809639700320598019290533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23746186267094130692387377 17809639700320598019290533)
                    ·
                      refine ⟨3339307443810112128616975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17809639700320598019290533 3339307443810112128616975)
                      ·
                        rfl

theorem cell23_6503278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_6503278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503278 prefixEnd_6503278 := by exact prefixLift 6503278
  have htrace : WordTrace (prefixWord ++ tailWord_6503278) baseStart_6503278 baseEnd_6503278 := by
    simpa [prefixWord, tailWord_6503278, baseEnd_6503278] using wordTrace_append hprefix tailTrace_6503278
  have hstable : (prefixWord ++ tailWord_6503278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503278).length < 2 ^ (prefixWord ++ tailWord_6503278).sum := by decide
  have hdescent : baseEnd_6503278 < baseStart_6503278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503281 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_6503281 : Nat := 118140960795 + 6503281 * 2 ^ 59
def prefixEnd_6503281 : Nat := 4983230072969 + 3 ^ 40 * 6503281 * 2
def baseEnd_6503281 : Nat := 3339308984252075616879461

theorem tailTrace_6503281 : CollatzResearch.WordTrace tailWord_6503281 prefixEnd_6503281 3339308984252075616879461 := by
  unfold tailWord_6503281
  simp only [CollatzResearch.WordTrace]
  refine ⟨237194144352731083814797697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158129429568487389209865131 237194144352731083814797697)
  ·
    refine ⟨177895608264548312861098273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237194144352731083814797697 177895608264548312861098273)
    ·
      refine ⟨133421706198411234645823705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177895608264548312861098273 133421706198411234645823705)
      ·
        refine ⟨100066279648808425984367779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133421706198411234645823705 100066279648808425984367779)
        ·
          refine ⟨150099419473212638976551669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100066279648808425984367779 150099419473212638976551669)
          ·
            refine ⟨14071820575613684904051719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150099419473212638976551669 14071820575613684904051719)
            ·
              refine ⟨21107730863420527356077579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14071820575613684904051719 21107730863420527356077579)
              ·
                refine ⟨31661596295130791034116369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21107730863420527356077579 31661596295130791034116369)
                ·
                  refine ⟨23746197221348093275587277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31661596295130791034116369 23746197221348093275587277)
                  ·
                    refine ⟨8904823958005534978345229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23746197221348093275587277 8904823958005534978345229)
                    ·
                      refine ⟨3339308984252075616879461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8904823958005534978345229 3339308984252075616879461)
                      ·
                        rfl

theorem cell23_6503281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_6503281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503281 prefixEnd_6503281 := by exact prefixLift 6503281
  have htrace : WordTrace (prefixWord ++ tailWord_6503281) baseStart_6503281 baseEnd_6503281 := by
    simpa [prefixWord, tailWord_6503281, baseEnd_6503281] using wordTrace_append hprefix tailTrace_6503281
  have hstable : (prefixWord ++ tailWord_6503281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503281).length < 2 ^ (prefixWord ++ tailWord_6503281).sum := by decide
  have hdescent : baseEnd_6503281 < baseStart_6503281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503301 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_6503301 : Nat := 118140960795 + 6503301 * 2 ^ 59
def prefixEnd_6503301 : Nat := 4983230072969 + 3 ^ 40 * 6503301 * 2
def baseEnd_6503301 : Nat := 1113106417955055179543123

theorem tailTrace_6503301 : CollatzResearch.WordTrace tailWord_6503301 prefixEnd_6503301 1113106417955055179543123 := by
  unfold tailWord_6503301
  simp only [CollatzResearch.WordTrace]
  refine ⟨237194873812658627230525757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158129915875105751487017171 237194873812658627230525757)
  ·
    refine ⟨88948077679746985211447159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237194873812658627230525757 88948077679746985211447159)
    ·
      refine ⟨133422116519620477817170739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88948077679746985211447159 133422116519620477817170739)
      ·
        refine ⟨200133174779430716725756109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133422116519620477817170739 200133174779430716725756109)
        ·
          refine ⟨75049940542286518772158541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200133174779430716725756109 75049940542286518772158541)
          ·
            refine ⟨28143727703357444539559453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75049940542286518772158541 28143727703357444539559453)
            ·
              refine ⟨10553897888759041702334795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28143727703357444539559453 10553897888759041702334795)
              ·
                refine ⟨15830846833138562553502193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10553897888759041702334795 15830846833138562553502193)
                ·
                  refine ⟨11873135124853921915126645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15830846833138562553502193 11873135124853921915126645)
                  ·
                    refine ⟨1113106417955055179543123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11873135124853921915126645 1113106417955055179543123)
                    ·
                      rfl

theorem cell23_6503301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_6503301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503301 prefixEnd_6503301 := by exact prefixLift 6503301
  have htrace : WordTrace (prefixWord ++ tailWord_6503301) baseStart_6503301 baseEnd_6503301 := by
    simpa [prefixWord, tailWord_6503301, baseEnd_6503301] using wordTrace_append hprefix tailTrace_6503301
  have hstable : (prefixWord ++ tailWord_6503301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503301).length < 2 ^ (prefixWord ++ tailWord_6503301).sum := by decide
  have hdescent : baseEnd_6503301 < baseStart_6503301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503331 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 3, 4]
def baseStart_6503331 : Nat := 118140960795 + 6503331 * 2 ^ 59
def prefixEnd_6503331 : Nat := 4983230072969 + 3 ^ 40 * 6503331 * 2
def baseEnd_6503331 : Nat := 1113111552761600140418077

theorem tailTrace_6503331 : CollatzResearch.WordTrace tailWord_6503331 prefixEnd_6503331 1113111552761600140418077 := by
  unfold tailWord_6503331
  simp only [CollatzResearch.WordTrace]
  refine ⟨237195968002549942354117847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158130645335033294902745231 237195968002549942354117847)
  ·
    refine ⟨355793952003824913531176771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237195968002549942354117847 355793952003824913531176771)
    ·
      refine ⟨533690928005737370296765157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355793952003824913531176771 533690928005737370296765157)
      ·
        refine ⟨100067049001075756930643467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 533690928005737370296765157 100067049001075756930643467)
        ·
          refine ⟨150100573501613635395965201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100067049001075756930643467 150100573501613635395965201)
          ·
            refine ⟨112575430126210226546973901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150100573501613635395965201 112575430126210226546973901)
            ·
              refine ⟨42215786297328834955115213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112575430126210226546973901 42215786297328834955115213)
              ·
                refine ⟨15830919861498313108168205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42215786297328834955115213 15830919861498313108168205)
                ·
                  refine ⟨5936594948061867415563077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15830919861498313108168205 5936594948061867415563077)
                  ·
                    refine ⟨1113111552761600140418077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936594948061867415563077 1113111552761600140418077)
                    ·
                      rfl

theorem cell23_6503331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 4].length) (baseStart_6503331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503331 prefixEnd_6503331 := by exact prefixLift 6503331
  have htrace : WordTrace (prefixWord ++ tailWord_6503331) baseStart_6503331 baseEnd_6503331 := by
    simpa [prefixWord, tailWord_6503331, baseEnd_6503331] using wordTrace_append hprefix tailTrace_6503331
  have hstable : (prefixWord ++ tailWord_6503331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503331).length < 2 ^ (prefixWord ++ tailWord_6503331).sum := by decide
  have hdescent : baseEnd_6503331 < baseStart_6503331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503358 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_6503358 : Nat := 118140960795 + 6503358 * 2 ^ 59
def prefixEnd_6503358 : Nat := 4983230072969 + 3 ^ 40 * 6503358 * 2
def baseEnd_6503358 : Nat := 3339348522262471815616607

theorem tailTrace_6503358 : CollatzResearch.WordTrace tailWord_6503358 prefixEnd_6503358 3339348522262471815616607 := by
  unfold tailWord_6503358
  simp only [CollatzResearch.WordTrace]
  refine ⟨29649619096681515745668841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158131301848968083976900485 29649619096681515745668841)
  ·
    refine ⟨22237214322511136809251631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29649619096681515745668841 22237214322511136809251631)
    ·
      refine ⟨33355821483766705213877447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22237214322511136809251631 33355821483766705213877447)
      ·
        refine ⟨50033732225650057820816171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33355821483766705213877447 50033732225650057820816171)
        ·
          refine ⟨75050598338475086731224257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50033732225650057820816171 75050598338475086731224257)
          ·
            refine ⟨56287948753856315048418193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75050598338475086731224257 56287948753856315048418193)
            ·
              refine ⟨42215961565392236286313645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56287948753856315048418193 42215961565392236286313645)
              ·
                refine ⟨15830985587022088607367617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42215961565392236286313645 15830985587022088607367617)
                ·
                  refine ⟨11873239190266566455525713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15830985587022088607367617 11873239190266566455525713)
                  ·
                    refine ⟨8904929392699924841644285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11873239190266566455525713 8904929392699924841644285)
                    ·
                      refine ⟨3339348522262471815616607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8904929392699924841644285 3339348522262471815616607)
                      ·
                        rfl

theorem cell23_6503358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_6503358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503358 prefixEnd_6503358 := by exact prefixLift 6503358
  have htrace : WordTrace (prefixWord ++ tailWord_6503358) baseStart_6503358 baseEnd_6503358 := by
    simpa [prefixWord, tailWord_6503358, baseEnd_6503358] using wordTrace_append hprefix tailTrace_6503358
  have hstable : (prefixWord ++ tailWord_6503358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503358).length < 2 ^ (prefixWord ++ tailWord_6503358).sum := by decide
  have hdescent : baseEnd_6503358 < baseStart_6503358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503382 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_6503382 : Nat := 118140960795 + 6503382 * 2 ^ 59
def prefixEnd_6503382 : Nat := 4983230072969 + 3 ^ 40 * 6503382 * 2
def baseEnd_6503382 : Nat := 1113120281932726573905499

theorem tailTrace_6503382 : CollatzResearch.WordTrace tailWord_6503382 prefixEnd_6503382 1113120281932726573905499 := by
  unfold tailWord_6503382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14824864257835323629014025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158131885416910118709482933 14824864257835323629014025)
  ·
    refine ⟨11118648193376492721760519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14824864257835323629014025 11118648193376492721760519)
    ·
      refine ⟨16677972290064739082640779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11118648193376492721760519 16677972290064739082640779)
      ·
        refine ⟨25016958435097108623961169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16677972290064739082640779 25016958435097108623961169)
        ·
          refine ⟨18762718826322831467970877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25016958435097108623961169 18762718826322831467970877)
          ·
            refine ⟨7036019559871061800489079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18762718826322831467970877 7036019559871061800489079)
            ·
              refine ⟨10554029339806592700733619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7036019559871061800489079 10554029339806592700733619)
              ·
                refine ⟨15831044009709889051100429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10554029339806592700733619 15831044009709889051100429)
                ·
                  refine ⟨5936641503641208394162661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15831044009709889051100429 5936641503641208394162661)
                  ·
                    refine ⟨1113120281932726573905499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936641503641208394162661 1113120281932726573905499)
                    ·
                      rfl

theorem cell23_6503382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_6503382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503382 prefixEnd_6503382 := by exact prefixLift 6503382
  have htrace : WordTrace (prefixWord ++ tailWord_6503382) baseStart_6503382 baseEnd_6503382 := by
    simpa [prefixWord, tailWord_6503382, baseEnd_6503382] using wordTrace_append hprefix tailTrace_6503382
  have hstable : (prefixWord ++ tailWord_6503382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503382).length < 2 ^ (prefixWord ++ tailWord_6503382).sum := by decide
  have hdescent : baseEnd_6503382 < baseStart_6503382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503425 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 1, 5]
def baseStart_6503425 : Nat := 118140960795 + 6503425 * 2 ^ 59
def prefixEnd_6503425 : Nat := 4983230072969 + 3 ^ 40 * 6503425 * 2
def baseEnd_6503425 : Nat := 1113127641822107684492933

theorem tailTrace_6503425 : CollatzResearch.WordTrace tailWord_6503425 prefixEnd_6503425 1113127641822107684492933 := by
  unfold tailWord_6503425
  simp only [CollatzResearch.WordTrace]
  refine ⟨237199396464209396408039729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158132930976139597605359819 237199396464209396408039729)
  ·
    refine ⟨177899547348157047306029797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237199396464209396408039729 177899547348157047306029797)
    ·
      refine ⟨33356165127779446369880587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177899547348157047306029797 33356165127779446369880587)
      ·
        refine ⟨50034247691669169554820881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33356165127779446369880587 50034247691669169554820881)
        ·
          refine ⟨37525685768751877166115661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50034247691669169554820881 37525685768751877166115661)
          ·
            refine ⟨14072132163281953937293373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37525685768751877166115661 14072132163281953937293373)
            ·
              refine ⟨5277049561230732726485015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14072132163281953937293373 5277049561230732726485015)
              ·
                refine ⟨7915574341846099089727523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277049561230732726485015 7915574341846099089727523)
                ·
                  refine ⟨11873361512769148634591285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7915574341846099089727523 11873361512769148634591285)
                  ·
                    refine ⟨1113127641822107684492933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11873361512769148634591285 1113127641822107684492933)
                    ·
                      rfl

theorem cell23_6503425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_6503425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503425 prefixEnd_6503425 := by exact prefixLift 6503425
  have htrace : WordTrace (prefixWord ++ tailWord_6503425) baseStart_6503425 baseEnd_6503425 := by
    simpa [prefixWord, tailWord_6503425, baseEnd_6503425] using wordTrace_append hprefix tailTrace_6503425
  have hstable : (prefixWord ++ tailWord_6503425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503425).length < 2 ^ (prefixWord ++ tailWord_6503425).sum := by decide
  have hdescent : baseEnd_6503425 < baseStart_6503425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503448 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_6503448 : Nat := 118140960795 + 6503448 * 2 ^ 59
def prefixEnd_6503448 : Nat := 4983230072969 + 3 ^ 40 * 6503448 * 2
def baseEnd_6503448 : Nat := 3339394735521376463491193

theorem tailTrace_6503448 : CollatzResearch.WordTrace tailWord_6503448 prefixEnd_6503448 3339394735521376463491193 := by
  unfold tailWord_6503448
  simp only [CollatzResearch.WordTrace]
  refine ⟨118600117671563035668063499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158133490228750714224084665 118600117671563035668063499)
  ·
    refine ⟨177900176507344553502095249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118600117671563035668063499 177900176507344553502095249)
    ·
      refine ⟨133425132380508415126571437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177900176507344553502095249 133425132380508415126571437)
      ·
        refine ⟨50034424642690655672464289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133425132380508415126571437 50034424642690655672464289)
        ·
          refine ⟨37525818482017991754348217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50034424642690655672464289 37525818482017991754348217)
          ·
            refine ⟨28144363861513493815761163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37525818482017991754348217 28144363861513493815761163)
            ·
              refine ⟨42216545792270240723641745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28144363861513493815761163 42216545792270240723641745)
              ·
                refine ⟨31662409344202680542731309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42216545792270240723641745 31662409344202680542731309)
                ·
                  refine ⟨11873403504076005203524241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31662409344202680542731309 11873403504076005203524241)
                  ·
                    refine ⟨8905052628057003902643181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11873403504076005203524241 8905052628057003902643181)
                    ·
                      refine ⟨3339394735521376463491193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905052628057003902643181 3339394735521376463491193)
                      ·
                        rfl

theorem cell23_6503448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_6503448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503448 prefixEnd_6503448 := by exact prefixLift 6503448
  have htrace : WordTrace (prefixWord ++ tailWord_6503448) baseStart_6503448 baseEnd_6503448 := by
    simpa [prefixWord, tailWord_6503448, baseEnd_6503448] using wordTrace_append hprefix tailTrace_6503448
  have hstable : (prefixWord ++ tailWord_6503448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503448).length < 2 ^ (prefixWord ++ tailWord_6503448).sum := by decide
  have hdescent : baseEnd_6503448 < baseStart_6503448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503458 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_6503458 : Nat := 118140960795 + 6503458 * 2 ^ 59
def prefixEnd_6503458 : Nat := 4983230072969 + 3 ^ 40 * 6503458 * 2
def baseEnd_6503458 : Nat := 3339399870327921424366147

theorem tailTrace_6503458 : CollatzResearch.WordTrace tailWord_6503458 prefixEnd_6503458 3339399870327921424366147 := by
  unfold tailWord_6503458
  simp only [CollatzResearch.WordTrace]
  refine ⟨59300150018272460760997757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158133733382059895362660685 59300150018272460760997757)
  ·
    refine ⟨22237556256852172785374159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59300150018272460760997757 22237556256852172785374159)
    ·
      refine ⟨33356334385278259178061239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22237556256852172785374159 33356334385278259178061239)
      ·
        refine ⟨50034501577917388767091859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33356334385278259178061239 50034501577917388767091859)
        ·
          refine ⟨75051752366876083150637789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50034501577917388767091859 75051752366876083150637789)
          ·
            refine ⟨28144407137578531181489171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75051752366876083150637789 28144407137578531181489171)
            ·
              refine ⟨42216610706367796772233757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28144407137578531181489171 42216610706367796772233757)
              ·
                refine ⟨15831229014887923789587659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42216610706367796772233757 15831229014887923789587659)
                ·
                  refine ⟨23746843522331885684381489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15831229014887923789587659 23746843522331885684381489)
                  ·
                    refine ⟨17810132641748914263286117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23746843522331885684381489 17810132641748914263286117)
                    ·
                      refine ⟨3339399870327921424366147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17810132641748914263286117 3339399870327921424366147)
                      ·
                        rfl

theorem cell23_6503458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_6503458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503458 prefixEnd_6503458 := by exact prefixLift 6503458
  have htrace : WordTrace (prefixWord ++ tailWord_6503458) baseStart_6503458 baseEnd_6503458 := by
    simpa [prefixWord, tailWord_6503458, baseEnd_6503458] using wordTrace_append hprefix tailTrace_6503458
  have hstable : (prefixWord ++ tailWord_6503458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503458).length < 2 ^ (prefixWord ++ tailWord_6503458).sum := by decide
  have hdescent : baseEnd_6503458 < baseStart_6503458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503489 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6503489 : Nat := 118140960795 + 6503489 * 2 ^ 59
def prefixEnd_6503489 : Nat := 4983230072969 + 3 ^ 40 * 6503489 * 2
def baseEnd_6503489 : Nat := 1113138596076070267692835

theorem tailTrace_6503489 : CollatzResearch.WordTrace tailWord_6503489 prefixEnd_6503489 1113138596076070267692835 := by
  unfold tailWord_6503489
  simp only [CollatzResearch.WordTrace]
  refine ⟨237201730735977535338369521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158134487157318356892246347 237201730735977535338369521)
  ·
    refine ⟨177901298051983151503777141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237201730735977535338369521 177901298051983151503777141)
    ·
      refine ⟨16678246692373420453479107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177901298051983151503777141 16678246692373420453479107)
      ·
        refine ⟨25017370038560130680218661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678246692373420453479107 25017370038560130680218661)
        ·
          refine ⟨4690756882230024502540999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25017370038560130680218661 4690756882230024502540999)
          ·
            refine ⟨7036135323345036753811499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690756882230024502540999 7036135323345036753811499)
            ·
              refine ⟨10554202985017555130717249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7036135323345036753811499 10554202985017555130717249)
              ·
                refine ⟨7915652238763166348037937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10554202985017555130717249 7915652238763166348037937)
                ·
                  refine ⟨5936739179072374761028453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7915652238763166348037937 5936739179072374761028453)
                  ·
                    refine ⟨1113138596076070267692835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936739179072374761028453 1113138596076070267692835)
                    ·
                      rfl

theorem cell23_6503489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6503489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503489 prefixEnd_6503489 := by exact prefixLift 6503489
  have htrace : WordTrace (prefixWord ++ tailWord_6503489) baseStart_6503489 baseEnd_6503489 := by
    simpa [prefixWord, tailWord_6503489, baseEnd_6503489] using wordTrace_append hprefix tailTrace_6503489
  have hstable : (prefixWord ++ tailWord_6503489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503489).length < 2 ^ (prefixWord ++ tailWord_6503489).sum := by decide
  have hdescent : baseEnd_6503489 < baseStart_6503489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503495 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_6503495 : Nat := 118140960795 + 6503495 * 2 ^ 59
def prefixEnd_6503495 : Nat := 4983230072969 + 3 ^ 40 * 6503495 * 2
def baseEnd_6503495 : Nat := 3339418869112137779603477

theorem tailTrace_6503495 : CollatzResearch.WordTrace tailWord_6503495 prefixEnd_6503495 3339418869112137779603477 := by
  unfold tailWord_6503495
  simp only [CollatzResearch.WordTrace]
  refine ⟨237201949573955798363087939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158134633049303865575391959 237201949573955798363087939)
  ·
    refine ⟨355802924360933697544631909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237201949573955798363087939 355802924360933697544631909)
    ·
      refine ⟨66713048317675068289618483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355802924360933697544631909 66713048317675068289618483)
      ·
        refine ⟨100069572476512602434427725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66713048317675068289618483 100069572476512602434427725)
        ·
          refine ⟨37526089678692225912910397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100069572476512602434427725 37526089678692225912910397)
          ·
            refine ⟨14072283629509584717341399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37526089678692225912910397 14072283629509584717341399)
            ·
              refine ⟨21108425444264377076012099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14072283629509584717341399 21108425444264377076012099)
              ·
                refine ⟨31662638166396565614018149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21108425444264377076012099 31662638166396565614018149)
                ·
                  refine ⟨5936744656199356052628403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31662638166396565614018149 5936744656199356052628403)
                  ·
                    refine ⟨8905116984299034078942605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5936744656199356052628403 8905116984299034078942605)
                    ·
                      refine ⟨3339418869112137779603477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905116984299034078942605 3339418869112137779603477)
                      ·
                        rfl

theorem cell23_6503495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_6503495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503495 prefixEnd_6503495 := by exact prefixLift 6503495
  have htrace : WordTrace (prefixWord ++ tailWord_6503495) baseStart_6503495 baseEnd_6503495 := by
    simpa [prefixWord, tailWord_6503495, baseEnd_6503495] using wordTrace_append hprefix tailTrace_6503495
  have hstable : (prefixWord ++ tailWord_6503495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503495).length < 2 ^ (prefixWord ++ tailWord_6503495).sum := by decide
  have hdescent : baseEnd_6503495 < baseStart_6503495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503512 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_6503512 : Nat := 118140960795 + 6503512 * 2 ^ 59
def prefixEnd_6503512 : Nat := 4983230072969 + 3 ^ 40 * 6503512 * 2
def baseEnd_6503512 : Nat := 3339427598283264213090899

theorem tailTrace_6503512 : CollatzResearch.WordTrace tailWord_6503512 prefixEnd_6503512 3339427598283264213090899 := by
  unfold tailWord_6503512
  simp only [CollatzResearch.WordTrace]
  refine ⟨118601284807447105133228395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158135046409929473510971193 118601284807447105133228395)
  ·
    refine ⟨177901927211170657699842593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118601284807447105133228395 177901927211170657699842593)
    ·
      refine ⟨133426445408377993274881945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177901927211170657699842593 133426445408377993274881945)
      ·
        refine ⟨100069834056283494956161459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133426445408377993274881945 100069834056283494956161459)
        ·
          refine ⟨150104751084425242434242189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100069834056283494956161459 150104751084425242434242189)
          ·
            refine ⟨56289281656659465912840821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150104751084425242434242189 56289281656659465912840821)
            ·
              refine ⟨5277120155311824929328827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56289281656659465912840821 5277120155311824929328827)
              ·
                refine ⟨7915680232967737393993241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277120155311824929328827 7915680232967737393993241)
                ·
                  refine ⟨5936760174725803045494931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7915680232967737393993241 5936760174725803045494931)
                  ·
                    refine ⟨8905140262088704568242397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5936760174725803045494931 8905140262088704568242397)
                    ·
                      refine ⟨3339427598283264213090899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905140262088704568242397 3339427598283264213090899)
                      ·
                        rfl

theorem cell23_6503512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_6503512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503512 prefixEnd_6503512 := by exact prefixLift 6503512
  have htrace : WordTrace (prefixWord ++ tailWord_6503512) baseStart_6503512 baseEnd_6503512 := by
    simpa [prefixWord, tailWord_6503512, baseEnd_6503512] using wordTrace_append hprefix tailTrace_6503512
  have hstable : (prefixWord ++ tailWord_6503512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503512).length < 2 ^ (prefixWord ++ tailWord_6503512).sum := by decide
  have hdescent : baseEnd_6503512 < baseStart_6503512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503535 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 6, 2, 2]
def baseStart_6503535 : Nat := 118140960795 + 6503535 * 2 ^ 59
def prefixEnd_6503535 : Nat := 4983230072969 + 3 ^ 40 * 6503535 * 2
def baseEnd_6503535 : Nat := 3339439408338317623103293

theorem tailTrace_6503535 : CollatzResearch.WordTrace tailWord_6503535 prefixEnd_6503535 3339439408338317623103293 := by
  unfold tailWord_6503535
  simp only [CollatzResearch.WordTrace]
  refine ⟨237203408493810885194544059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158135605662540590129696039 237203408493810885194544059)
  ·
    refine ⟨355805112740716327791816089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237203408493810885194544059 355805112740716327791816089)
    ·
      refine ⟨266853834555537245843862067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355805112740716327791816089 266853834555537245843862067)
      ·
        refine ⟨400280751833305868765793101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266853834555537245843862067 400280751833305868765793101)
        ·
          refine ⟨150105281937489700787172413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400280751833305868765793101 150105281937489700787172413)
          ·
            refine ⟨56289480726558637795189655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150105281937489700787172413 56289480726558637795189655)
            ·
              refine ⟨84434221089837956692784483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56289480726558637795189655 84434221089837956692784483)
              ·
                refine ⟨126651331634756935039176725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84434221089837956692784483 126651331634756935039176725)
                ·
                  refine ⟨5936781170379231329961409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126651331634756935039176725 5936781170379231329961409)
                  ·
                    refine ⟨4452585877784423497471057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5936781170379231329961409 4452585877784423497471057)
                    ·
                      refine ⟨3339439408338317623103293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452585877784423497471057 3339439408338317623103293)
                      ·
                        rfl

theorem cell23_6503535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 2, 2].length) (baseStart_6503535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503535 prefixEnd_6503535 := by exact prefixLift 6503535
  have htrace : WordTrace (prefixWord ++ tailWord_6503535) baseStart_6503535 baseEnd_6503535 := by
    simpa [prefixWord, tailWord_6503535, baseEnd_6503535] using wordTrace_append hprefix tailTrace_6503535
  have hstable : (prefixWord ++ tailWord_6503535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503535).length < 2 ^ (prefixWord ++ tailWord_6503535).sum := by decide
  have hdescent : baseEnd_6503535 < baseStart_6503535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503538 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6503538 : Nat := 118140960795 + 6503538 * 2 ^ 59
def prefixEnd_6503538 : Nat := 4983230072969 + 3 ^ 40 * 6503538 * 2
def baseEnd_6503538 : Nat := 3339440948780281111365779

theorem tailTrace_6503538 : CollatzResearch.WordTrace tailWord_6503538 prefixEnd_6503538 3339440948780281111365779 := by
  unfold tailWord_6503538
  simp only [CollatzResearch.WordTrace]
  refine ⟨59300879478200004176725817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158135678608533344471268845 59300879478200004176725817)
  ·
    refine ⟨44475659608650003132544363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59300879478200004176725817 44475659608650003132544363)
    ·
      refine ⟨66713489412975004698816545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44475659608650003132544363 66713489412975004698816545)
      ·
        refine ⟨50035117059731253524112409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66713489412975004698816545 50035117059731253524112409)
        ·
          refine ⟨37526337794798440143084307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50035117059731253524112409 37526337794798440143084307)
          ·
            refine ⟨56289506692197660214626461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37526337794798440143084307 56289506692197660214626461)
            ·
              refine ⟨21108565009574122580484923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56289506692197660214626461 21108565009574122580484923)
              ·
                refine ⟨31662847514361183870727385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21108565009574122580484923 31662847514361183870727385)
                ·
                  refine ⟨23747135635770887903045539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31662847514361183870727385 23747135635770887903045539)
                  ·
                    refine ⟨35620703453656331854568309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23747135635770887903045539 35620703453656331854568309)
                    ·
                      refine ⟨3339440948780281111365779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35620703453656331854568309 3339440948780281111365779)
                      ·
                        rfl

theorem cell23_6503538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6503538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503538 prefixEnd_6503538 := by exact prefixLift 6503538
  have htrace : WordTrace (prefixWord ++ tailWord_6503538) baseStart_6503538 baseEnd_6503538 := by
    simpa [prefixWord, tailWord_6503538, baseEnd_6503538] using wordTrace_append hprefix tailTrace_6503538
  have hstable : (prefixWord ++ tailWord_6503538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503538).length < 2 ^ (prefixWord ++ tailWord_6503538).sum := by decide
  have hdescent : baseEnd_6503538 < baseStart_6503538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503571 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 7]
def baseStart_6503571 : Nat := 118140960795 + 6503571 * 2 ^ 59
def prefixEnd_6503571 : Nat := 4983230072969 + 3 ^ 40 * 6503571 * 2
def baseEnd_6503571 : Nat := 1113152631213959827417709

theorem tailTrace_6503571 : CollatzResearch.WordTrace tailWord_6503571 prefixEnd_6503571 1113152631213959827417709 := by
  unfold tailWord_6503571
  simp only [CollatzResearch.WordTrace]
  refine ⟨237204721521680463342854567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158136481014453642228569711 237204721521680463342854567)
  ·
    refine ⟨355807082282520695014281851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237204721521680463342854567 355807082282520695014281851)
    ·
      refine ⟨533710623423781042521422777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355807082282520695014281851 533710623423781042521422777)
      ·
        refine ⟨400282967567835781891067083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533710623423781042521422777 400282967567835781891067083)
        ·
          refine ⟨600424451351753672836600625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400282967567835781891067083 600424451351753672836600625)
          ·
            refine ⟨450318338513815254627450469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600424451351753672836600625 450318338513815254627450469)
            ·
              refine ⟨84434688471340360242646963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450318338513815254627450469 84434688471340360242646963)
              ·
                refine ⟨126652032707010540363970445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84434688471340360242646963 126652032707010540363970445)
                ·
                  refine ⟨47494512265128952636488917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126652032707010540363970445 47494512265128952636488917)
                  ·
                    refine ⟨1113152631213959827417709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47494512265128952636488917 1113152631213959827417709)
                    ·
                      rfl

theorem cell23_6503571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_6503571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503571 prefixEnd_6503571 := by exact prefixLift 6503571
  have htrace : WordTrace (prefixWord ++ tailWord_6503571) baseStart_6503571 baseEnd_6503571 := by
    simpa [prefixWord, tailWord_6503571, baseEnd_6503571] using wordTrace_append hprefix tailTrace_6503571
  have hstable : (prefixWord ++ tailWord_6503571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503571).length < 2 ^ (prefixWord ++ tailWord_6503571).sum := by decide
  have hdescent : baseEnd_6503571 < baseStart_6503571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503608 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_6503608 : Nat := 118140960795 + 6503608 * 2 ^ 59
def prefixEnd_6503608 : Nat := 4983230072969 + 3 ^ 40 * 6503608 * 2
def baseEnd_6503608 : Nat := 3339476892426095837490457

theorem tailTrace_6503608 : CollatzResearch.WordTrace tailWord_6503608 prefixEnd_6503608 3339476892426095837490457 := by
  unfold tailWord_6503608
  simp only [CollatzResearch.WordTrace]
  refine ⟨118603035511273209330975739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158137380681697612441300985 118603035511273209330975739)
  ·
    refine ⟨177904553266909813996463609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118603035511273209330975739 177904553266909813996463609)
    ·
      refine ⟨133428414950182360497347707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177904553266909813996463609 133428414950182360497347707)
      ·
        refine ⟨200142622425273540746021561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133428414950182360497347707 200142622425273540746021561)
        ·
          refine ⟨150106966818955155559516171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200142622425273540746021561 150106966818955155559516171)
          ·
            refine ⟨225160450228432733339274257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150106966818955155559516171 225160450228432733339274257)
            ·
              refine ⟨168870337671324550004455693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225160450228432733339274257 168870337671324550004455693)
              ·
                refine ⟨63326376626746706251670885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168870337671324550004455693 63326376626746706251670885)
                ·
                  refine ⟨11873695617515007422188291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63326376626746706251670885 11873695617515007422188291)
                  ·
                    refine ⟨17810543426272511133282437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11873695617515007422188291 17810543426272511133282437)
                    ·
                      refine ⟨3339476892426095837490457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17810543426272511133282437 3339476892426095837490457)
                      ·
                        rfl

theorem cell23_6503608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_6503608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503608 prefixEnd_6503608 := by exact prefixLift 6503608
  have htrace : WordTrace (prefixWord ++ tailWord_6503608) baseStart_6503608 baseEnd_6503608 := by
    simpa [prefixWord, tailWord_6503608, baseEnd_6503608] using wordTrace_append hprefix tailTrace_6503608
  have hstable : (prefixWord ++ tailWord_6503608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503608).length < 2 ^ (prefixWord ++ tailWord_6503608).sum := by decide
  have hdescent : baseEnd_6503608 < baseStart_6503608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503652 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_6503652 : Nat := 118140960795 + 6503652 * 2 ^ 59
def prefixEnd_6503652 : Nat := 4983230072969 + 3 ^ 40 * 6503652 * 2
def baseEnd_6503652 : Nat := 1113166495191631221780085

theorem tailTrace_6503652 : CollatzResearch.WordTrace tailWord_6503652 prefixEnd_6503652 1113166495191631221780085 := by
  unfold tailWord_6503652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118603837917193507088276605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158138450556258009451035473 118603837917193507088276605)
  ·
    refine ⟨44476439218947565158103727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118603837917193507088276605 44476439218947565158103727)
    ·
      refine ⟨66714658828421347737155591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44476439218947565158103727 66714658828421347737155591)
      ·
        refine ⟨100071988242632021605733387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66714658828421347737155591 100071988242632021605733387)
        ·
          refine ⟨150107982363948032408600081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100071988242632021605733387 150107982363948032408600081)
          ·
            refine ⟨112580986772961024306450061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150107982363948032408600081 112580986772961024306450061)
            ·
              refine ⟨42217870039860384114918773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112580986772961024306450061 42217870039860384114918773)
              ·
                refine ⟨3957925316236911010773635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42217870039860384114918773 3957925316236911010773635)
                ·
                  refine ⟨5936887974355366516160453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957925316236911010773635 5936887974355366516160453)
                  ·
                    refine ⟨1113166495191631221780085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5936887974355366516160453 1113166495191631221780085)
                    ·
                      rfl

theorem cell23_6503652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_6503652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503652 prefixEnd_6503652 := by exact prefixLift 6503652
  have htrace : WordTrace (prefixWord ++ tailWord_6503652) baseStart_6503652 baseEnd_6503652 := by
    simpa [prefixWord, tailWord_6503652, baseEnd_6503652] using wordTrace_append hprefix tailTrace_6503652
  have hstable : (prefixWord ++ tailWord_6503652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503652).length < 2 ^ (prefixWord ++ tailWord_6503652).sum := by decide
  have hdescent : baseEnd_6503652 < baseStart_6503652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503685 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_6503685 : Nat := 118140960795 + 6503685 * 2 ^ 59
def prefixEnd_6503685 : Nat := 4983230072969 + 3 ^ 40 * 6503685 * 2
def baseEnd_6503685 : Nat := 3339516430436492036227603

theorem tailTrace_6503685 : CollatzResearch.WordTrace tailWord_6503685 prefixEnd_6503685 3339516430436492036227603 := by
  unfold tailWord_6503685
  simp only [CollatzResearch.WordTrace]
  refine ⟨237208879443267460812504509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158139252962178307208336339 237208879443267460812504509)
  ·
    refine ⟨88953329791225297804689191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237208879443267460812504509 88953329791225297804689191)
    ·
      refine ⟨133429994686837946707033787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88953329791225297804689191 133429994686837946707033787)
      ·
        refine ⟨200144992030256920060550681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133429994686837946707033787 200144992030256920060550681)
        ·
          refine ⟨150108744022692690045413011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200144992030256920060550681 150108744022692690045413011)
          ·
            refine ⟨225163116034039035068119517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150108744022692690045413011 225163116034039035068119517)
            ·
              refine ⟨84436168512764638150544819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225163116034039035068119517 84436168512764638150544819)
              ·
                refine ⟨126654252769146957225817229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84436168512764638150544819 126654252769146957225817229)
                ·
                  refine ⟨47495344788430108959681461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126654252769146957225817229 47495344788430108959681461)
                  ·
                    refine ⟨4452688573915322714970137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47495344788430108959681461 4452688573915322714970137)
                    ·
                      refine ⟨3339516430436492036227603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452688573915322714970137 3339516430436492036227603)
                      ·
                        rfl

theorem cell23_6503685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_6503685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503685 prefixEnd_6503685 := by exact prefixLift 6503685
  have htrace : WordTrace (prefixWord ++ tailWord_6503685) baseStart_6503685 baseEnd_6503685 := by
    simpa [prefixWord, tailWord_6503685, baseEnd_6503685] using wordTrace_append hprefix tailTrace_6503685
  have hstable : (prefixWord ++ tailWord_6503685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503685).length < 2 ^ (prefixWord ++ tailWord_6503685).sum := by decide
  have hdescent : baseEnd_6503685 < baseStart_6503685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503692 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_6503692 : Nat := 118140960795 + 6503692 * 2 ^ 59
def prefixEnd_6503692 : Nat := 4983230072969 + 3 ^ 40 * 6503692 * 2
def baseEnd_6503692 : Nat := 3339520024801073508840071

theorem tailTrace_6503692 : CollatzResearch.WordTrace tailWord_6503692 prefixEnd_6503692 3339520024801073508840071 := by
  unfold tailWord_6503692
  simp only [CollatzResearch.WordTrace]
  refine ⟨118604567377121050504004665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158139423169494734005339553 118604567377121050504004665)
  ·
    refine ⟨88953425532840787878003499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118604567377121050504004665 88953425532840787878003499)
    ·
      refine ⟨133430138299261181817005249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88953425532840787878003499 133430138299261181817005249)
      ·
        refine ⟨100072603724445886362753937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133430138299261181817005249 100072603724445886362753937)
        ·
          refine ⟨75054452793334414772065453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100072603724445886362753937 75054452793334414772065453)
          ·
            refine ⟨28145419797500405539524545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75054452793334414772065453 28145419797500405539524545)
            ·
              refine ⟨21109064848125304154643409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28145419797500405539524545 21109064848125304154643409)
              ·
                refine ⟨15831798636093978115982557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21109064848125304154643409 15831798636093978115982557)
                ·
                  refine ⟨5936924488535241793493459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15831798636093978115982557 5936924488535241793493459)
                  ·
                    refine ⟨8905386732802862690240189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5936924488535241793493459 8905386732802862690240189)
                    ·
                      refine ⟨3339520024801073508840071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905386732802862690240189 3339520024801073508840071)
                      ·
                        rfl

theorem cell23_6503692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_6503692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503692 prefixEnd_6503692 := by exact prefixLift 6503692
  have htrace : WordTrace (prefixWord ++ tailWord_6503692) baseStart_6503692 baseEnd_6503692 := by
    simpa [prefixWord, tailWord_6503692, baseEnd_6503692] using wordTrace_append hprefix tailTrace_6503692
  have hstable : (prefixWord ++ tailWord_6503692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503692).length < 2 ^ (prefixWord ++ tailWord_6503692).sum := by decide
  have hdescent : baseEnd_6503692 < baseStart_6503692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503728 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_6503728 : Nat := 118140960795 + 6503728 * 2 ^ 59
def prefixEnd_6503728 : Nat := 4983230072969 + 3 ^ 40 * 6503728 * 2
def baseEnd_6503728 : Nat := 3339538510104635367989905

theorem tailTrace_6503728 : CollatzResearch.WordTrace tailWord_6503728 prefixEnd_6503728 3339538510104635367989905 := by
  unfold tailWord_6503728
  simp only [CollatzResearch.WordTrace]
  refine ⟨118605223891055839578159919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158140298521407786104213225 118605223891055839578159919)
  ·
    refine ⟨177907835836583759367239879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118605223891055839578159919 177907835836583759367239879)
    ·
      refine ⟨266861753754875639050859819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177907835836583759367239879 266861753754875639050859819)
      ·
        refine ⟨400292630632313458576289729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266861753754875639050859819 400292630632313458576289729)
        ·
          refine ⟨300219472974235093932217297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400292630632313458576289729 300219472974235093932217297)
          ·
            refine ⟨225164604730676320449162973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300219472974235093932217297 225164604730676320449162973)
            ·
              refine ⟨84436726774003620168436115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225164604730676320449162973 84436726774003620168436115)
              ·
                refine ⟨126655090161005430252654173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84436726774003620168436115 126655090161005430252654173)
                ·
                  refine ⟨47495658810377036344745315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126655090161005430252654173 47495658810377036344745315)
                  ·
                    refine ⟨71243488215565554517117973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47495658810377036344745315 71243488215565554517117973)
                    ·
                      refine ⟨3339538510104635367989905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71243488215565554517117973 3339538510104635367989905)
                      ·
                        rfl

theorem cell23_6503728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_6503728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503728 prefixEnd_6503728 := by exact prefixLift 6503728
  have htrace : WordTrace (prefixWord ++ tailWord_6503728) baseStart_6503728 baseEnd_6503728 := by
    simpa [prefixWord, tailWord_6503728, baseEnd_6503728] using wordTrace_append hprefix tailTrace_6503728
  have hstable : (prefixWord ++ tailWord_6503728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503728).length < 2 ^ (prefixWord ++ tailWord_6503728).sum := by decide
  have hdescent : baseEnd_6503728 < baseStart_6503728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503732 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6503732 : Nat := 118140960795 + 6503732 * 2 ^ 59
def prefixEnd_6503732 : Nat := 4983230072969 + 3 ^ 40 * 6503732 * 2
def baseEnd_6503732 : Nat := 3339540564027253352339887

theorem tailTrace_6503732 : CollatzResearch.WordTrace tailWord_6503732 prefixEnd_6503732 3339540564027253352339887 := by
  unfold tailWord_6503732
  simp only [CollatzResearch.WordTrace]
  refine ⟨118605296837048593919732725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158140395782731458559643633 118605296837048593919732725)
  ·
    refine ⟨11119246578473305679974943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118605296837048593919732725 11119246578473305679974943)
    ·
      refine ⟨16678869867709958519962415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11119246578473305679974943 16678869867709958519962415)
      ·
        refine ⟨25018304801564937779943623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16678869867709958519962415 25018304801564937779943623)
        ·
          refine ⟨37527457202347406669915435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25018304801564937779943623 37527457202347406669915435)
          ·
            refine ⟨56291185803521110004873153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37527457202347406669915435 56291185803521110004873153)
            ·
              refine ⟨42218389352640832503654865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56291185803521110004873153 42218389352640832503654865)
              ·
                refine ⟨31663792014480624377741149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42218389352640832503654865 31663792014480624377741149)
                ·
                  refine ⟨11873922005430234141652931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31663792014480624377741149 11873922005430234141652931)
                  ·
                    refine ⟨17810883008145351212479397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11873922005430234141652931 17810883008145351212479397)
                    ·
                      refine ⟨3339540564027253352339887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17810883008145351212479397 3339540564027253352339887)
                      ·
                        rfl

theorem cell23_6503732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6503732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503732 prefixEnd_6503732 := by exact prefixLift 6503732
  have htrace : WordTrace (prefixWord ++ tailWord_6503732) baseStart_6503732 baseEnd_6503732 := by
    simpa [prefixWord, tailWord_6503732, baseEnd_6503732] using wordTrace_append hprefix tailTrace_6503732
  have hstable : (prefixWord ++ tailWord_6503732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503732).length < 2 ^ (prefixWord ++ tailWord_6503732).sum := by decide
  have hdescent : baseEnd_6503732 < baseStart_6503732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503783 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_6503783 : Nat := 118140960795 + 6503783 * 2 ^ 59
def prefixEnd_6503783 : Nat := 4983230072969 + 3 ^ 40 * 6503783 * 2
def baseEnd_6503783 : Nat := 3339566751540632652802153

theorem tailTrace_6503783 : CollatzResearch.WordTrace tailWord_6503783 prefixEnd_6503783 3339566751540632652802153 := by
  unfold tailWord_6503783
  simp only [CollatzResearch.WordTrace]
  refine ⟨237212453796912423549572003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158141635864608282366381335 237212453796912423549572003)
  ·
    refine ⟨355818680695368635324358005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237212453796912423549572003 355818680695368635324358005)
    ·
      refine ⟨33358001315190809561658563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355818680695368635324358005 33358001315190809561658563)
      ·
        refine ⟨50037001972786214342487845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33358001315190809561658563 50037001972786214342487845)
        ·
          refine ⟨9381937869897415189216471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50037001972786214342487845 9381937869897415189216471)
          ·
            refine ⟨14072906804846122783824707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381937869897415189216471 14072906804846122783824707)
            ·
              refine ⟨21109360207269184175737061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14072906804846122783824707 21109360207269184175737061)
              ·
                refine ⟨3958005038862972032950699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21109360207269184175737061 3958005038862972032950699)
                ·
                  refine ⟨5937007558294458049426049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958005038862972032950699 5937007558294458049426049)
                  ·
                    refine ⟨4452755668720843537069537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5937007558294458049426049 4452755668720843537069537)
                    ·
                      refine ⟨3339566751540632652802153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452755668720843537069537 3339566751540632652802153)
                      ·
                        rfl

theorem cell23_6503783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_6503783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503783 prefixEnd_6503783 := by exact prefixLift 6503783
  have htrace : WordTrace (prefixWord ++ tailWord_6503783) baseStart_6503783 baseEnd_6503783 := by
    simpa [prefixWord, tailWord_6503783, baseEnd_6503783] using wordTrace_append hprefix tailTrace_6503783
  have hstable : (prefixWord ++ tailWord_6503783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503783).length < 2 ^ (prefixWord ++ tailWord_6503783).sum := by decide
  have hdescent : baseEnd_6503783 < baseStart_6503783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503792 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2]
def baseStart_6503792 : Nat := 118140960795 + 6503792 * 2 ^ 59
def prefixEnd_6503792 : Nat := 4983230072969 + 3 ^ 40 * 6503792 * 2
def baseEnd_6503792 : Nat := 3339571372866523117589611

theorem tailTrace_6503792 : CollatzResearch.WordTrace tailWord_6503792 prefixEnd_6503792 3339571372866523117589611 := by
  unfold tailWord_6503792
  simp only [CollatzResearch.WordTrace]
  refine ⟨118606391026939909043324815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158141854702586545391099753 118606391026939909043324815)
  ·
    refine ⟨177909586540409863564987223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118606391026939909043324815 177909586540409863564987223)
    ·
      refine ⟨266864379810614795347480835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177909586540409863564987223 266864379810614795347480835)
      ·
        refine ⟨400296569715922193021221253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266864379810614795347480835 400296569715922193021221253)
        ·
          refine ⟨75055606821735411191478985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400296569715922193021221253 75055606821735411191478985)
          ·
            refine ⟨56291705116301558393609239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75055606821735411191478985 56291705116301558393609239)
            ·
              refine ⟨84437557674452337590413859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56291705116301558393609239 84437557674452337590413859)
              ·
                refine ⟨126656336511678506385620789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84437557674452337590413859 126656336511678506385620789)
                ·
                  refine ⟨11874031547969859973651949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126656336511678506385620789 11874031547969859973651949)
                  ·
                    refine ⟨4452761830488697490119481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11874031547969859973651949 4452761830488697490119481)
                    ·
                      refine ⟨3339571372866523117589611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4452761830488697490119481 3339571372866523117589611)
                      ·
                        rfl

theorem cell23_6503792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 3, 2].length) (baseStart_6503792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503792 prefixEnd_6503792 := by exact prefixLift 6503792
  have htrace : WordTrace (prefixWord ++ tailWord_6503792) baseStart_6503792 baseEnd_6503792 := by
    simpa [prefixWord, tailWord_6503792, baseEnd_6503792] using wordTrace_append hprefix tailTrace_6503792
  have hstable : (prefixWord ++ tailWord_6503792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503792).length < 2 ^ (prefixWord ++ tailWord_6503792).sum := by decide
  have hdescent : baseEnd_6503792 < baseStart_6503792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503805 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_6503805 : Nat := 118140960795 + 6503805 * 2 ^ 59
def prefixEnd_6503805 : Nat := 4983230072969 + 3 ^ 40 * 6503805 * 2
def baseEnd_6503805 : Nat := 3339578048115031566727051

theorem tailTrace_6503805 : CollatzResearch.WordTrace tailWord_6503805 prefixEnd_6503805 3339578048115031566727051 := by
  unfold tailWord_6503805
  simp only [CollatzResearch.WordTrace]
  refine ⟨237213256202832721306872869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158142170801888480871248579 237213256202832721306872869)
  ·
    refine ⟨44477485538031135245038663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237213256202832721306872869 44477485538031135245038663)
    ·
      refine ⟨66716228307046702867557995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44477485538031135245038663 66716228307046702867557995)
      ·
        refine ⟨100074342460570054301336993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66716228307046702867557995 100074342460570054301336993)
        ·
          refine ⟨75055756845427540726002745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100074342460570054301336993 75055756845427540726002745)
          ·
            refine ⟨56291817634070655544502059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75055756845427540726002745 56291817634070655544502059)
            ·
              refine ⟨84437726451105983316753089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56291817634070655544502059 84437726451105983316753089)
              ·
                refine ⟨63328294838329487487564817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84437726451105983316753089 63328294838329487487564817)
                ·
                  refine ⟨47496221128747115615673613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63328294838329487487564817 47496221128747115615673613)
                  ·
                    refine ⟨17811082923280168355877605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47496221128747115615673613 17811082923280168355877605)
                    ·
                      refine ⟨3339578048115031566727051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17811082923280168355877605 3339578048115031566727051)
                      ·
                        rfl

theorem cell23_6503805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_6503805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503805 prefixEnd_6503805 := by exact prefixLift 6503805
  have htrace : WordTrace (prefixWord ++ tailWord_6503805) baseStart_6503805 baseEnd_6503805 := by
    simpa [prefixWord, tailWord_6503805, baseEnd_6503805] using wordTrace_append hprefix tailTrace_6503805
  have hstable : (prefixWord ++ tailWord_6503805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503805).length < 2 ^ (prefixWord ++ tailWord_6503805).sum := by decide
  have hdescent : baseEnd_6503805 < baseStart_6503805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503806 : List Nat := [4, 2, 3, 2, 1, 1, 3, 7]
def baseStart_6503806 : Nat := 118140960795 + 6503806 * 2 ^ 59
def prefixEnd_6503806 : Nat := 4983230072969 + 3 ^ 40 * 6503806 * 2
def baseEnd_6503806 : Nat := 123688094873914298622761

theorem tailTrace_6503806 : CollatzResearch.WordTrace tailWord_6503806 prefixEnd_6503806 123688094873914298622761 := by
  unfold tailWord_6503806
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651661584478637309707409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158142195117219398985106181 29651661584478637309707409)
  ·
    refine ⟨22238746188358977982280557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29651661584478637309707409 22238746188358977982280557)
    ·
      refine ⟨8339529820634616743355209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22238746188358977982280557 8339529820634616743355209)
      ·
        refine ⟨6254647365475962557516407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8339529820634616743355209 6254647365475962557516407)
        ·
          refine ⟨9381971048213943836274611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6254647365475962557516407 9381971048213943836274611)
          ·
            refine ⟨14072956572320915754411917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9381971048213943836274611 14072956572320915754411917)
            ·
              refine ⟨5277358714620343407904469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14072956572320915754411917 5277358714620343407904469)
              ·
                refine ⟨123688094873914298622761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5277358714620343407904469 123688094873914298622761)
                ·
                  rfl

theorem cell23_6503806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_6503806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503806 prefixEnd_6503806 := by exact prefixLift 6503806
  have htrace : WordTrace (prefixWord ++ tailWord_6503806) baseStart_6503806 baseEnd_6503806 := by
    simpa [prefixWord, tailWord_6503806, baseEnd_6503806] using wordTrace_append hprefix tailTrace_6503806
  have hstable : (prefixWord ++ tailWord_6503806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503806).length < 2 ^ (prefixWord ++ tailWord_6503806).sum := by decide
  have hdescent : baseEnd_6503806 < baseStart_6503806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503825 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_6503825 : Nat := 118140960795 + 6503825 * 2 ^ 59
def prefixEnd_6503825 : Nat := 4983230072969 + 3 ^ 40 * 6503825 * 2
def baseEnd_6503825 : Nat := 3339588317728121488476959

theorem tailTrace_6503825 : CollatzResearch.WordTrace tailWord_6503825 prefixEnd_6503825 3339588317728121488476959 := by
  unfold tailWord_6503825
  simp only [CollatzResearch.WordTrace]
  refine ⟨237213985662760264722600929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158142657108506843148400619 237213985662760264722600929)
  ·
    refine ⟨177910489247070198541950697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237213985662760264722600929 177910489247070198541950697)
    ·
      refine ⟨133432866935302648906463023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177910489247070198541950697 133432866935302648906463023)
      ·
        refine ⟨200149300402953973359694535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133432866935302648906463023 200149300402953973359694535)
        ·
          refine ⟨300223950604430960039541803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200149300402953973359694535 300223950604430960039541803)
          ·
            refine ⟨450335925906646440059312705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300223950604430960039541803 450335925906646440059312705)
            ·
              refine ⟨337751944429984830044484529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450335925906646440059312705 337751944429984830044484529)
              ·
                refine ⟨253313958322488622533363397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337751944429984830044484529 253313958322488622533363397)
                ·
                  refine ⟨47496367185466616725005637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253313958322488622533363397 47496367185466616725005637)
                  ·
                    refine ⟨8905568847274990635938557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47496367185466616725005637 8905568847274990635938557)
                    ·
                      refine ⟨3339588317728121488476959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905568847274990635938557 3339588317728121488476959)
                      ·
                        rfl

theorem cell23_6503825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_6503825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503825 prefixEnd_6503825 := by exact prefixLift 6503825
  have htrace : WordTrace (prefixWord ++ tailWord_6503825) baseStart_6503825 baseEnd_6503825 := by
    simpa [prefixWord, tailWord_6503825, baseEnd_6503825] using wordTrace_append hprefix tailTrace_6503825
  have hstable : (prefixWord ++ tailWord_6503825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503825).length < 2 ^ (prefixWord ++ tailWord_6503825).sum := by decide
  have hdescent : baseEnd_6503825 < baseStart_6503825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503875 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 7]
def baseStart_6503875 : Nat := 118140960795 + 6503875 * 2 ^ 59
def prefixEnd_6503875 : Nat := 4983230072969 + 3 ^ 40 * 6503875 * 2
def baseEnd_6503875 : Nat := 1113204663920282097617243

theorem tailTrace_6503875 : CollatzResearch.WordTrace tailWord_6503875 prefixEnd_6503875 1113204663920282097617243 := by
  unfold tailWord_6503875
  simp only [CollatzResearch.WordTrace]
  refine ⟨237215809312579123261921079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158143872875052748841280719 237215809312579123261921079)
  ·
    refine ⟨355823713968868684892881619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237215809312579123261921079 355823713968868684892881619)
    ·
      refine ⟨533735570953303027339322429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355823713968868684892881619 533735570953303027339322429)
      ·
        refine ⟨200150839107488635252245911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533735570953303027339322429 200150839107488635252245911)
        ·
          refine ⟨300226258661232952878368867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200150839107488635252245911 300226258661232952878368867)
          ·
            refine ⟨450339387991849429317553301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300226258661232952878368867 450339387991849429317553301)
            ·
              refine ⟨21109658812117941999260311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 450339387991849429317553301 21109658812117941999260311)
              ·
                refine ⟨31664488218176912998890467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21109658812117941999260311 31664488218176912998890467)
                ·
                  refine ⟨47496732327265369498335701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31664488218176912998890467 47496732327265369498335701)
                  ·
                    refine ⟨1113204663920282097617243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47496732327265369498335701 1113204663920282097617243)
                    ·
                      rfl

theorem cell23_6503875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_6503875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503875 prefixEnd_6503875 := by exact prefixLift 6503875
  have htrace : WordTrace (prefixWord ++ tailWord_6503875) baseStart_6503875 baseEnd_6503875 := by
    simpa [prefixWord, tailWord_6503875, baseEnd_6503875] using wordTrace_append hprefix tailTrace_6503875
  have hstable : (prefixWord ++ tailWord_6503875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503875).length < 2 ^ (prefixWord ++ tailWord_6503875).sum := by decide
  have hdescent : baseEnd_6503875 < baseStart_6503875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503912 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6503912 : Nat := 118140960795 + 6503912 * 2 ^ 59
def prefixEnd_6503912 : Nat := 4983230072969 + 3 ^ 40 * 6503912 * 2
def baseEnd_6503912 : Nat := 3339632990545062648089059

theorem tailTrace_6503912 : CollatzResearch.WordTrace tailWord_6503912 prefixEnd_6503912 3339632990545062648089059 := by
  unfold tailWord_6503912
  simp only [CollatzResearch.WordTrace]
  refine ⟨118608579406722539290508995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158144772542296719054011993 118608579406722539290508995)
  ·
    refine ⟨177912869110083808935763493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118608579406722539290508995 177912869110083808935763493)
    ·
      refine ⟨33358662958140714175455655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177912869110083808935763493 33358662958140714175455655)
      ·
        refine ⟨50037994437211071263183483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33358662958140714175455655 50037994437211071263183483)
        ·
          refine ⟨75056991655816606894775225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50037994437211071263183483 75056991655816606894775225)
          ·
            refine ⟨56292743741862455171081419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75056991655816606894775225 56292743741862455171081419)
            ·
              refine ⟨84439115612793682756622129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56292743741862455171081419 84439115612793682756622129)
              ·
                refine ⟨63329336709595262067466597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84439115612793682756622129 63329336709595262067466597)
                ·
                  refine ⟨11874250633049111637649987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63329336709595262067466597 11874250633049111637649987)
                  ·
                    refine ⟨17811375949573667456474981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11874250633049111637649987 17811375949573667456474981)
                    ·
                      refine ⟨3339632990545062648089059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17811375949573667456474981 3339632990545062648089059)
                      ·
                        rfl

theorem cell23_6503912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6503912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503912 prefixEnd_6503912 := by exact prefixLift 6503912
  have htrace : WordTrace (prefixWord ++ tailWord_6503912) baseStart_6503912 baseEnd_6503912 := by
    simpa [prefixWord, tailWord_6503912, baseEnd_6503912] using wordTrace_append hprefix tailTrace_6503912
  have hstable : (prefixWord ++ tailWord_6503912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503912).length < 2 ^ (prefixWord ++ tailWord_6503912).sum := by decide
  have hdescent : baseEnd_6503912 < baseStart_6503912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503932 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_6503932 : Nat := 118140960795 + 6503932 * 2 ^ 59
def prefixEnd_6503932 : Nat := 4983230072969 + 3 ^ 40 * 6503932 * 2
def baseEnd_6503932 : Nat := 3339643260158152569838967

theorem tailTrace_6503932 : CollatzResearch.WordTrace tailWord_6503932 prefixEnd_6503932 3339643260158152569838967 := by
  unfold tailWord_6503932
  simp only [CollatzResearch.WordTrace]
  refine ⟨118608944136686310998373025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158145258848915081331164033 118608944136686310998373025)
  ·
    refine ⟨88956708102514733248779769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118608944136686310998373025 88956708102514733248779769)
    ·
      refine ⟨66717531076886049936584827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88956708102514733248779769 66717531076886049936584827)
      ·
        refine ⟨100076296615329074904877241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66717531076886049936584827 100076296615329074904877241)
        ·
          refine ⟨75057222461496806178657931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100076296615329074904877241 75057222461496806178657931)
          ·
            refine ⟨112585833692245209267986897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75057222461496806178657931 112585833692245209267986897)
            ·
              refine ⟨84439375269183906950990173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112585833692245209267986897 84439375269183906950990173)
              ·
                refine ⟨31664765725943965106621315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84439375269183906950990173 31664765725943965106621315)
                ·
                  refine ⟨47497148588915947659931973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31664765725943965106621315 47497148588915947659931973)
                  ·
                    refine ⟨8905715360421740186237245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47497148588915947659931973 8905715360421740186237245)
                    ·
                      refine ⟨3339643260158152569838967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905715360421740186237245 3339643260158152569838967)
                      ·
                        rfl

theorem cell23_6503932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_6503932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503932 prefixEnd_6503932 := by exact prefixLift 6503932
  have htrace : WordTrace (prefixWord ++ tailWord_6503932) baseStart_6503932 baseEnd_6503932 := by
    simpa [prefixWord, tailWord_6503932, baseEnd_6503932] using wordTrace_append hprefix tailTrace_6503932
  have hstable : (prefixWord ++ tailWord_6503932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503932).length < 2 ^ (prefixWord ++ tailWord_6503932).sum := by decide
  have hdescent : baseEnd_6503932 < baseStart_6503932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503935 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 8]
def baseStart_6503935 : Nat := 118140960795 + 6503935 * 2 ^ 59
def prefixEnd_6503935 : Nat := 4983230072969 + 3 ^ 40 * 6503935 * 2
def baseEnd_6503935 : Nat := 371071644511124006455717

theorem tailTrace_6503935 : CollatzResearch.WordTrace tailWord_6503935 prefixEnd_6503935 371071644511124006455717 := by
  unfold tailWord_6503935
  simp only [CollatzResearch.WordTrace]
  refine ⟨237217997692361753509105259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158145331794907835672736839 237217997692361753509105259)
  ·
    refine ⟨355826996538542630263657889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237217997692361753509105259 355826996538542630263657889)
    ·
      refine ⟨266870247403906972697743417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355826996538542630263657889 266870247403906972697743417)
      ·
        refine ⟨200152685552930229523307563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266870247403906972697743417 200152685552930229523307563)
        ·
          refine ⟨300229028329395344284961345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200152685552930229523307563 300229028329395344284961345)
          ·
            refine ⟨225171771247046508213721009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300229028329395344284961345 225171771247046508213721009)
            ·
              refine ⟨168878828435284881160290757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225171771247046508213721009 168878828435284881160290757)
              ·
                refine ⟨31664780331615915217554517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168878828435284881160290757 31664780331615915217554517)
                ·
                  refine ⟨371071644511124006455717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31664780331615915217554517 371071644511124006455717)
                  ·
                    rfl

theorem cell23_6503935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 8].length) (baseStart_6503935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503935 prefixEnd_6503935 := by exact prefixLift 6503935
  have htrace : WordTrace (prefixWord ++ tailWord_6503935) baseStart_6503935 baseEnd_6503935 := by
    simpa [prefixWord, tailWord_6503935, baseEnd_6503935] using wordTrace_append hprefix tailTrace_6503935
  have hstable : (prefixWord ++ tailWord_6503935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503935).length < 2 ^ (prefixWord ++ tailWord_6503935).sum := by decide
  have hdescent : baseEnd_6503935 < baseStart_6503935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503962 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_6503962 : Nat := 118140960795 + 6503962 * 2 ^ 59
def prefixEnd_6503962 : Nat := 4983230072969 + 3 ^ 40 * 6503962 * 2
def baseEnd_6503962 : Nat := 3339658664577787452463829

theorem tailTrace_6503962 : CollatzResearch.WordTrace tailWord_6503962 prefixEnd_6503962 3339658664577787452463829 := by
  unfold tailWord_6503962
  simp only [CollatzResearch.WordTrace]
  refine ⟨59304745615815984280084535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158145988308842624746892093 59304745615815984280084535)
  ·
    refine ⟨88957118423723976420126803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59304745615815984280084535 88957118423723976420126803)
    ·
      refine ⟨133435677635585964630190205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88957118423723976420126803 133435677635585964630190205)
      ·
        refine ⟨50038379113344736736321327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133435677635585964630190205 50038379113344736736321327)
        ·
          refine ⟨75057568670017105104481991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50038379113344736736321327 75057568670017105104481991)
          ·
            refine ⟨112586353005025657656722987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75057568670017105104481991 112586353005025657656722987)
            ·
              refine ⟨168879529507538486485084481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112586353005025657656722987 168879529507538486485084481)
              ·
                refine ⟨126659647130653864863813361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168879529507538486485084481 126659647130653864863813361)
                ·
                  refine ⟨94994735347990398647860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126659647130653864863813361 94994735347990398647860021)
                  ·
                    refine ⟨8905756438874099873236877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94994735347990398647860021 8905756438874099873236877)
                    ·
                      refine ⟨3339658664577787452463829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905756438874099873236877 3339658664577787452463829)
                      ·
                        rfl

theorem cell23_6503962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_6503962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503962 prefixEnd_6503962 := by exact prefixLift 6503962
  have htrace : WordTrace (prefixWord ++ tailWord_6503962) baseStart_6503962 baseEnd_6503962 := by
    simpa [prefixWord, tailWord_6503962, baseEnd_6503962] using wordTrace_append hprefix tailTrace_6503962
  have hstable : (prefixWord ++ tailWord_6503962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503962).length < 2 ^ (prefixWord ++ tailWord_6503962).sum := by decide
  have hdescent : baseEnd_6503962 < baseStart_6503962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503990 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6503990 : Nat := 118140960795 + 6503990 * 2 ^ 59
def prefixEnd_6503990 : Nat := 4983230072969 + 3 ^ 40 * 6503990 * 2
def baseEnd_6503990 : Nat := 1113224347345371114304567

theorem tailTrace_6503990 : CollatzResearch.WordTrace tailWord_6503990 prefixEnd_6503990 1113224347345371114304567 := by
  unfold tailWord_6503990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14826250231697656118897339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158146669138108331934904949 14826250231697656118897339)
  ·
    refine ⟨22239375347546484178346009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14826250231697656118897339 22239375347546484178346009)
    ·
      refine ⟨16679531510659863133759507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22239375347546484178346009 16679531510659863133759507)
      ·
        refine ⟨25019297265989794700639261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16679531510659863133759507 25019297265989794700639261)
        ·
          refine ⟨9382236474746173012739723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25019297265989794700639261 9382236474746173012739723)
          ·
            refine ⟨14073354712119259519109585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382236474746173012739723 14073354712119259519109585)
            ·
              refine ⟨10555016034089444639332189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14073354712119259519109585 10555016034089444639332189)
              ·
                refine ⟨3958131012783541739749571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10555016034089444639332189 3958131012783541739749571)
                ·
                  refine ⟨5937196519175312609624357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958131012783541739749571 5937196519175312609624357)
                  ·
                    refine ⟨1113224347345371114304567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937196519175312609624357 1113224347345371114304567)
                    ·
                      rfl

theorem cell23_6503990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6503990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503990 prefixEnd_6503990 := by exact prefixLift 6503990
  have htrace : WordTrace (prefixWord ++ tailWord_6503990) baseStart_6503990 baseEnd_6503990 := by
    simpa [prefixWord, tailWord_6503990, baseEnd_6503990] using wordTrace_append hprefix tailTrace_6503990
  have hstable : (prefixWord ++ tailWord_6503990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503990).length < 2 ^ (prefixWord ++ tailWord_6503990).sum := by decide
  have hdescent : baseEnd_6503990 < baseStart_6503990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6503999 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 1, 5]
def baseStart_6503999 : Nat := 118140960795 + 6503999 * 2 ^ 59
def prefixEnd_6503999 : Nat := 4983230072969 + 3 ^ 40 * 6503999 * 2
def baseEnd_6503999 : Nat := 1113225887787334602567053

theorem tailTrace_6503999 : CollatzResearch.WordTrace tailWord_6503999 prefixEnd_6503999 1113225887787334602567053 := by
  unfold tailWord_6503999
  simp only [CollatzResearch.WordTrace]
  refine ⟨237220331964129892439435051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158146887976086594959623367 237220331964129892439435051)
  ·
    refine ⟨355830497946194838659152577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237220331964129892439435051 355830497946194838659152577)
    ·
      refine ⟨266872873459646128994364433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355830497946194838659152577 266872873459646128994364433)
      ·
        refine ⟨200154655094734596745773325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266872873459646128994364433 200154655094734596745773325)
        ·
          refine ⟨75057995660525473779664997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200154655094734596745773325 75057995660525473779664997)
          ·
            refine ⟨14073374186348526333687187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75057995660525473779664997 14073374186348526333687187)
            ·
              refine ⟨21110061279522789500530781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14073374186348526333687187 21110061279522789500530781)
              ·
                refine ⟨7916272979821046062699043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21110061279522789500530781 7916272979821046062699043)
                ·
                  refine ⟨11874409469731569094048565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916272979821046062699043 11874409469731569094048565)
                  ·
                    refine ⟨1113225887787334602567053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11874409469731569094048565 1113225887787334602567053)
                    ·
                      rfl

theorem cell23_6503999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_6503999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6503999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6503999 prefixEnd_6503999 := by exact prefixLift 6503999
  have htrace : WordTrace (prefixWord ++ tailWord_6503999) baseStart_6503999 baseEnd_6503999 := by
    simpa [prefixWord, tailWord_6503999, baseEnd_6503999] using wordTrace_append hprefix tailTrace_6503999
  have hstable : (prefixWord ++ tailWord_6503999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6503999).length < 2 ^ (prefixWord ++ tailWord_6503999).sum := by decide
  have hdescent : baseEnd_6503999 < baseStart_6503999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6503999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504036 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_6504036 : Nat := 118140960795 + 6504036 * 2 ^ 59
def prefixEnd_6504036 : Nat := 4983230072969 + 3 ^ 40 * 6504036 * 2
def baseEnd_6504036 : Nat := 3339696662146220162938489

theorem tailTrace_6504036 : CollatzResearch.WordTrace tailWord_6504036 prefixEnd_6504036 3339696662146220162938489 := by
  unfold tailWord_6504036
  simp only [CollatzResearch.WordTrace]
  refine ⟨118610840732497923879265981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158147787643330565172354641 118610840732497923879265981)
  ·
    refine ⟨44479065274686721454724743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118610840732497923879265981 44479065274686721454724743)
    ·
      refine ⟨66718597912030082182087115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44479065274686721454724743 66718597912030082182087115)
      ·
        refine ⟨100077896868045123273130673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66718597912030082182087115 100077896868045123273130673)
        ·
          refine ⟨75058422651033842454848005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100077896868045123273130673 75058422651033842454848005)
          ·
            refine ⟨14073454247068845460284001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75058422651033842454848005 14073454247068845460284001)
            ·
              refine ⟨10555090685301634095213001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14073454247068845460284001 10555090685301634095213001)
              ·
                refine ⟨7916318013976225571409751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10555090685301634095213001 7916318013976225571409751)
                ·
                  refine ⟨11874477020964338357114627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916318013976225571409751 11874477020964338357114627)
                  ·
                    refine ⟨17811715531446507535671941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11874477020964338357114627 17811715531446507535671941)
                    ·
                      refine ⟨3339696662146220162938489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17811715531446507535671941 3339696662146220162938489)
                      ·
                        rfl

theorem cell23_6504036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_6504036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504036 prefixEnd_6504036 := by exact prefixLift 6504036
  have htrace : WordTrace (prefixWord ++ tailWord_6504036) baseStart_6504036 baseEnd_6504036 := by
    simpa [prefixWord, tailWord_6504036, baseEnd_6504036] using wordTrace_append hprefix tailTrace_6504036
  have hstable : (prefixWord ++ tailWord_6504036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504036).length < 2 ^ (prefixWord ++ tailWord_6504036).sum := by decide
  have hdescent : baseEnd_6504036 < baseStart_6504036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504039 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_6504039 : Nat := 118140960795 + 6504039 * 2 ^ 59
def prefixEnd_6504039 : Nat := 4983230072969 + 3 ^ 40 * 6504039 * 2
def baseEnd_6504039 : Nat := 3339698202588183651200975

theorem tailTrace_6504039 : CollatzResearch.WordTrace tailWord_6504039 prefixEnd_6504039 3339698202588183651200975 := by
  unfold tailWord_6504039
  simp only [CollatzResearch.WordTrace]
  refine ⟨237221790883984979270891171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158147860589323319513927447 237221790883984979270891171)
  ·
    refine ⟨355832686325977468906336757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237221790883984979270891171 355832686325977468906336757)
    ·
      refine ⟨33359314343060387709969071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355832686325977468906336757 33359314343060387709969071)
      ·
        refine ⟨50038971514590581564953607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33359314343060387709969071 50038971514590581564953607)
        ·
          refine ⟨75058457271885872347430411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50038971514590581564953607 75058457271885872347430411)
          ·
            refine ⟨112587685907828808521145617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75058457271885872347430411 112587685907828808521145617)
            ·
              refine ⟨84440764430871606390859213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112587685907828808521145617 84440764430871606390859213)
              ·
                refine ⟨31665286661576852396572205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84440764430871606390859213 31665286661576852396572205)
                ·
                  refine ⟨11874482498091319648714577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31665286661576852396572205 11874482498091319648714577)
                  ·
                    refine ⟨8905861873568489736535933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11874482498091319648714577 8905861873568489736535933)
                    ·
                      refine ⟨3339698202588183651200975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8905861873568489736535933 3339698202588183651200975)
                      ·
                        rfl

theorem cell23_6504039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_6504039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504039 prefixEnd_6504039 := by exact prefixLift 6504039
  have htrace : WordTrace (prefixWord ++ tailWord_6504039) baseStart_6504039 baseEnd_6504039 := by
    simpa [prefixWord, tailWord_6504039, baseEnd_6504039] using wordTrace_append hprefix tailTrace_6504039
  have hstable : (prefixWord ++ tailWord_6504039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504039).length < 2 ^ (prefixWord ++ tailWord_6504039).sum := by decide
  have hdescent : baseEnd_6504039 < baseStart_6504039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504159 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_6504159 : Nat := 118140960795 + 6504159 * 2 ^ 59
def prefixEnd_6504159 : Nat := 4983230072969 + 3 ^ 40 * 6504159 * 2
def baseEnd_6504159 : Nat := 3339759820266723181700423

theorem tailTrace_6504159 : CollatzResearch.WordTrace tailWord_6504159 prefixEnd_6504159 3339759820266723181700423 := by
  unfold tailWord_6504159
  simp only [CollatzResearch.WordTrace]
  refine ⟨237226167643550239765259531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158150778429033493176839687 237226167643550239765259531)
  ·
    refine ⟨355839251465325359647889297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237226167643550239765259531 355839251465325359647889297)
    ·
      refine ⟨266879438598994019735916973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355839251465325359647889297 266879438598994019735916973)
      ·
        refine ⟨100079789474622757400968865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266879438598994019735916973 100079789474622757400968865)
        ·
          refine ⟨75059842105967068050726649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100079789474622757400968865 75059842105967068050726649)
          ·
            refine ⟨56294881579475301038044987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75059842105967068050726649 56294881579475301038044987)
            ·
              refine ⟨84442322369212951557067481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56294881579475301038044987 84442322369212951557067481)
              ·
                refine ⟨63331741776909713667800611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84442322369212951557067481 63331741776909713667800611)
                ·
                  refine ⟨94997612665364570501700917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63331741776909713667800611 94997612665364570501700917)
                  ·
                    refine ⟨8906026187377928484534461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94997612665364570501700917 8906026187377928484534461)
                    ·
                      refine ⟨3339759820266723181700423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906026187377928484534461 3339759820266723181700423)
                      ·
                        rfl

theorem cell23_6504159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_6504159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504159 prefixEnd_6504159 := by exact prefixLift 6504159
  have htrace : WordTrace (prefixWord ++ tailWord_6504159) baseStart_6504159 baseEnd_6504159 := by
    simpa [prefixWord, tailWord_6504159, baseEnd_6504159] using wordTrace_append hprefix tailTrace_6504159
  have hstable : (prefixWord ++ tailWord_6504159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504159).length < 2 ^ (prefixWord ++ tailWord_6504159).sum := by decide
  have hdescent : baseEnd_6504159 < baseStart_6504159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504179 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 2, 5]
def baseStart_6504179 : Nat := 118140960795 + 6504179 * 2 ^ 59
def prefixEnd_6504179 : Nat := 4983230072969 + 3 ^ 40 * 6504179 * 2
def baseEnd_6504179 : Nat := 1113256696626604367816777

theorem tailTrace_6504179 : CollatzResearch.WordTrace tailWord_6504179 prefixEnd_6504179 1113256696626604367816777 := by
  unfold tailWord_6504179
  simp only [CollatzResearch.WordTrace]
  refine ⟨237226897103477783180987591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158151264735651855453991727 237226897103477783180987591)
  ·
    refine ⟨355840345655216674771481387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237226897103477783180987591 355840345655216674771481387)
    ·
      refine ⟨533760518482825012157222081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355840345655216674771481387 533760518482825012157222081)
      ·
        refine ⟨400320388862118759117916561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533760518482825012157222081 400320388862118759117916561)
        ·
          refine ⟨300240291646589069338437421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400320388862118759117916561 300240291646589069338437421)
          ·
            refine ⟨112590109367470901001914033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300240291646589069338437421 112590109367470901001914033)
            ·
              refine ⟨84442582025603175751435525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112590109367470901001914033 84442582025603175751435525)
              ·
                refine ⟨15832984129800595453394161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84442582025603175751435525 15832984129800595453394161)
                ·
                  refine ⟨11874738097350446590045621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15832984129800595453394161 11874738097350446590045621)
                  ·
                    refine ⟨1113256696626604367816777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11874738097350446590045621 1113256696626604367816777)
                    ·
                      rfl

theorem cell23_6504179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 5].length) (baseStart_6504179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504179 prefixEnd_6504179 := by exact prefixLift 6504179
  have htrace : WordTrace (prefixWord ++ tailWord_6504179) baseStart_6504179 baseEnd_6504179 := by
    simpa [prefixWord, tailWord_6504179, baseEnd_6504179] using wordTrace_append hprefix tailTrace_6504179
  have hstable : (prefixWord ++ tailWord_6504179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504179).length < 2 ^ (prefixWord ++ tailWord_6504179).sum := by decide
  have hdescent : baseEnd_6504179 < baseStart_6504179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504198 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6504198 : Nat := 118140960795 + 6504198 * 2 ^ 59
def prefixEnd_6504198 : Nat := 4983230072969 + 3 ^ 40 * 6504198 * 2
def baseEnd_6504198 : Nat := 3339779846012248529112745

theorem tailTrace_6504198 : CollatzResearch.WordTrace tailWord_6504198 prefixEnd_6504198 3339779846012248529112745 := by
  unfold tailWord_6504198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413362190325279669560289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158151726726939299617286165 7413362190325279669560289)
  ·
    refine ⟨5560021642743959752170217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7413362190325279669560289 5560021642743959752170217)
    ·
      refine ⟨4170016232057969814127663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5560021642743959752170217 4170016232057969814127663)
      ·
        refine ⟨6255024348086954721191495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170016232057969814127663 6255024348086954721191495)
        ·
          refine ⟨9382536522130432081787243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255024348086954721191495 9382536522130432081787243)
          ·
            refine ⟨14073804783195648122680865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382536522130432081787243 14073804783195648122680865)
            ·
              refine ⟨10555353587396736092010649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14073804783195648122680865 10555353587396736092010649)
              ·
                refine ⟨7916515190547552069007987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10555353587396736092010649 7916515190547552069007987)
                ·
                  refine ⟨11874772785821328103511981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916515190547552069007987 11874772785821328103511981)
                  ·
                    refine ⟨4453039794682998038816993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11874772785821328103511981 4453039794682998038816993)
                    ·
                      refine ⟨3339779846012248529112745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453039794682998038816993 3339779846012248529112745)
                      ·
                        rfl

theorem cell23_6504198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6504198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504198 prefixEnd_6504198 := by exact prefixLift 6504198
  have htrace : WordTrace (prefixWord ++ tailWord_6504198) baseStart_6504198 baseEnd_6504198 := by
    simpa [prefixWord, tailWord_6504198, baseEnd_6504198] using wordTrace_append hprefix tailTrace_6504198
  have hstable : (prefixWord ++ tailWord_6504198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504198).length < 2 ^ (prefixWord ++ tailWord_6504198).sum := by decide
  have hdescent : baseEnd_6504198 < baseStart_6504198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504216 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_6504216 : Nat := 118140960795 + 6504216 * 2 ^ 59
def prefixEnd_6504216 : Nat := 4983230072969 + 3 ^ 40 * 6504216 * 2
def baseEnd_6504216 : Nat := 3339789088664029458687661

theorem tailTrace_6504216 : CollatzResearch.WordTrace tailWord_6504216 prefixEnd_6504216 3339789088664029458687661 := by
  unfold tailWord_6504216
  simp only [CollatzResearch.WordTrace]
  refine ⟨118614123302171869250042251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158152164402895825666723001 118614123302171869250042251)
  ·
    refine ⟨177921184953257803875063377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118614123302171869250042251 177921184953257803875063377)
    ·
      refine ⟨133440888714943352906297533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177921184953257803875063377 133440888714943352906297533)
      ·
        refine ⟨50040333268103757339861575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133440888714943352906297533 50040333268103757339861575)
        ·
          refine ⟨75060499902155636009792363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50040333268103757339861575 75060499902155636009792363)
          ·
            refine ⟨112590749853233454014688545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75060499902155636009792363 112590749853233454014688545)
            ·
              refine ⟨84443062389925090511016409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112590749853233454014688545 84443062389925090511016409)
              ·
                refine ⟨63332296792443817883262307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84443062389925090511016409 63332296792443817883262307)
                ·
                  refine ⟨94998445188665726824893461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63332296792443817883262307 94998445188665726824893461)
                  ·
                    refine ⟨4453052118218705944916881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94998445188665726824893461 4453052118218705944916881)
                    ·
                      refine ⟨3339789088664029458687661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453052118218705944916881 3339789088664029458687661)
                      ·
                        rfl

theorem cell23_6504216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_6504216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504216 prefixEnd_6504216 := by exact prefixLift 6504216
  have htrace : WordTrace (prefixWord ++ tailWord_6504216) baseStart_6504216 baseEnd_6504216 := by
    simpa [prefixWord, tailWord_6504216, baseEnd_6504216] using wordTrace_append hprefix tailTrace_6504216
  have hstable : (prefixWord ++ tailWord_6504216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504216).length < 2 ^ (prefixWord ++ tailWord_6504216).sum := by decide
  have hdescent : baseEnd_6504216 < baseStart_6504216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504236 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_6504236 : Nat := 118140960795 + 6504236 * 2 ^ 59
def prefixEnd_6504236 : Nat := 4983230072969 + 3 ^ 40 * 6504236 * 2
def baseEnd_6504236 : Nat := 3339799358277119380437569

theorem tailTrace_6504236 : CollatzResearch.WordTrace tailWord_6504236 prefixEnd_6504236 3339799358277119380437569 := by
  unfold tailWord_6504236
  simp only [CollatzResearch.WordTrace]
  refine ⟨118614488032135640957906281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158152650709514187943875041 118614488032135640957906281)
  ·
    refine ⟨88960866024101730718429711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118614488032135640957906281 88960866024101730718429711)
    ·
      refine ⟨133441299036152596077644567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88960866024101730718429711 133441299036152596077644567)
      ·
        refine ⟨200161948554228894116466851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133441299036152596077644567 200161948554228894116466851)
        ·
          refine ⟨300242922831343341174700277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200161948554228894116466851 300242922831343341174700277)
          ·
            refine ⟨28147774015438438235128151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300242922831343341174700277 28147774015438438235128151)
            ·
              refine ⟨42221661023157657352692227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28147774015438438235128151 42221661023157657352692227)
              ·
                refine ⟨63332491534736486029038341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42221661023157657352692227 63332491534736486029038341)
                ·
                  refine ⟨11874842162763091130444689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63332491534736486029038341 11874842162763091130444689)
                  ·
                    refine ⟨8906131622072318347833517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11874842162763091130444689 8906131622072318347833517)
                    ·
                      refine ⟨3339799358277119380437569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906131622072318347833517 3339799358277119380437569)
                      ·
                        rfl

theorem cell23_6504236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_6504236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504236 prefixEnd_6504236 := by exact prefixLift 6504236
  have htrace : WordTrace (prefixWord ++ tailWord_6504236) baseStart_6504236 baseEnd_6504236 := by
    simpa [prefixWord, tailWord_6504236, baseEnd_6504236] using wordTrace_append hprefix tailTrace_6504236
  have hstable : (prefixWord ++ tailWord_6504236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504236).length < 2 ^ (prefixWord ++ tailWord_6504236).sum := by decide
  have hdescent : baseEnd_6504236 < baseStart_6504236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504299 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 5, 6]
def baseStart_6504299 : Nat := 118140960795 + 6504299 * 2 ^ 59
def prefixEnd_6504299 : Nat := 4983230072969 + 3 ^ 40 * 6504299 * 2
def baseEnd_6504299 : Nat := 1113277235852784211316593

theorem tailTrace_6504299 : CollatzResearch.WordTrace tailWord_6504299 prefixEnd_6504299 1113277235852784211316593 := by
  unfold tailWord_6504299
  simp only [CollatzResearch.WordTrace]
  refine ⟨237231273863043043675355951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158154182575362029116903967 237231273863043043675355951)
  ·
    refine ⟨355846910794564565513033927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237231273863043043675355951 355846910794564565513033927)
    ·
      refine ⟨533770366191846848269550891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355846910794564565513033927 533770366191846848269550891)
      ·
        refine ⟨800655549287770272404326337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533770366191846848269550891 800655549287770272404326337)
        ·
          refine ⟨600491661965827704303244753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800655549287770272404326337 600491661965827704303244753)
          ·
            refine ⟨450368746474370778227433565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600491661965827704303244753 450368746474370778227433565)
            ·
              refine ⟨168888279927889041835287587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450368746474370778227433565 168888279927889041835287587)
              ·
                refine ⟨253332419891833562752931381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168888279927889041835287587 253332419891833562752931381)
                ·
                  refine ⟨23749914364859396508087317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253332419891833562752931381 23749914364859396508087317)
                  ·
                    refine ⟨1113277235852784211316593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23749914364859396508087317 1113277235852784211316593)
                    ·
                      rfl

theorem cell23_6504299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_6504299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504299 prefixEnd_6504299 := by exact prefixLift 6504299
  have htrace : WordTrace (prefixWord ++ tailWord_6504299) baseStart_6504299 baseEnd_6504299 := by
    simpa [prefixWord, tailWord_6504299, baseEnd_6504299] using wordTrace_append hprefix tailTrace_6504299
  have hstable : (prefixWord ++ tailWord_6504299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504299).length < 2 ^ (prefixWord ++ tailWord_6504299).sum := by decide
  have hdescent : baseEnd_6504299 < baseStart_6504299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504316 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_6504316 : Nat := 118140960795 + 6504316 * 2 ^ 59
def prefixEnd_6504316 : Nat := 4983230072969 + 3 ^ 40 * 6504316 * 2
def baseEnd_6504316 : Nat := 1113280145576493022479067

theorem tailTrace_6504316 : CollatzResearch.WordTrace tailWord_6504316 prefixEnd_6504316 1113280145576493022479067 := by
  unfold tailWord_6504316
  simp only [CollatzResearch.WordTrace]
  refine ⟨118615946951990727789362401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158154595935987637052483201 118615946951990727789362401)
  ·
    refine ⟨88961960213993045842021801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118615946951990727789362401 88961960213993045842021801)
    ·
      refine ⟨66721470160494784381516351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88961960213993045842021801 66721470160494784381516351)
      ·
        refine ⟨100082205240742176572274527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66721470160494784381516351 100082205240742176572274527)
        ·
          refine ⟨150123307861113264858411791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100082205240742176572274527 150123307861113264858411791)
          ·
            refine ⟨225184961791669897287617687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150123307861113264858411791 225184961791669897287617687)
            ·
              refine ⟨337777442687504845931426531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225184961791669897287617687 337777442687504845931426531)
              ·
                refine ⟨506666164031257268897139797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337777442687504845931426531 506666164031257268897139797)
                ·
                  refine ⟨5937494109741296119888357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 506666164031257268897139797 5937494109741296119888357)
                  ·
                    refine ⟨1113280145576493022479067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937494109741296119888357 1113280145576493022479067)
                    ·
                      rfl

theorem cell23_6504316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_6504316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504316 prefixEnd_6504316 := by exact prefixLift 6504316
  have htrace : WordTrace (prefixWord ++ tailWord_6504316) baseStart_6504316 baseEnd_6504316 := by
    simpa [prefixWord, tailWord_6504316, baseEnd_6504316] using wordTrace_append hprefix tailTrace_6504316
  have hstable : (prefixWord ++ tailWord_6504316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504316).length < 2 ^ (prefixWord ++ tailWord_6504316).sum := by decide
  have hdescent : baseEnd_6504316 < baseStart_6504316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504327 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_6504327 : Nat := 118140960795 + 6504327 * 2 ^ 59
def prefixEnd_6504327 : Nat := 4983230072969 + 3 ^ 40 * 6504327 * 2
def baseEnd_6504327 : Nat := 3339846085016678524399651

theorem tailTrace_6504327 : CollatzResearch.WordTrace tailWord_6504327 prefixEnd_6504327 3339846085016678524399651 := by
  unfold tailWord_6504327
  simp only [CollatzResearch.WordTrace]
  refine ⟨237232295106941604457375235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158154863404627736304916823 237232295106941604457375235)
  ·
    refine ⟨355848442660412406686062853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237232295106941604457375235 355848442660412406686062853)
    ·
      refine ⟨66721582998827326253636785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355848442660412406686062853 66721582998827326253636785)
      ·
        refine ⟨50041187249120494690227589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66721582998827326253636785 50041187249120494690227589)
        ·
          refine ⟨9382722609210092754417673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50041187249120494690227589 9382722609210092754417673)
          ·
            refine ⟨7037041956907569565813255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9382722609210092754417673 7037041956907569565813255)
            ·
              refine ⟨10555562935361354348719883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037041956907569565813255 10555562935361354348719883)
              ·
                refine ⟨15833344403042031523079825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10555562935361354348719883 15833344403042031523079825)
                ·
                  refine ⟨11875008302281523642309869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15833344403042031523079825 11875008302281523642309869)
                  ·
                    refine ⟨4453128113355571365866201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11875008302281523642309869 4453128113355571365866201)
                    ·
                      refine ⟨3339846085016678524399651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453128113355571365866201 3339846085016678524399651)
                      ·
                        rfl

theorem cell23_6504327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_6504327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504327 prefixEnd_6504327 := by exact prefixLift 6504327
  have htrace : WordTrace (prefixWord ++ tailWord_6504327) baseStart_6504327 baseEnd_6504327 := by
    simpa [prefixWord, tailWord_6504327, baseEnd_6504327] using wordTrace_append hprefix tailTrace_6504327
  have hstable : (prefixWord ++ tailWord_6504327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504327).length < 2 ^ (prefixWord ++ tailWord_6504327).sum := by decide
  have hdescent : baseEnd_6504327 < baseStart_6504327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504339 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_6504339 : Nat := 118140960795 + 6504339 * 2 ^ 59
def prefixEnd_6504339 : Nat := 4983230072969 + 3 ^ 40 * 6504339 * 2
def baseEnd_6504339 : Nat := 3339852246784532477449595

theorem tailTrace_6504339 : CollatzResearch.WordTrace tailWord_6504339 prefixEnd_6504339 3339852246784532477449595 := by
  unfold tailWord_6504339
  simp only [CollatzResearch.WordTrace]
  refine ⟨237232732782898130506812071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158155155188598753671208047 237232732782898130506812071)
  ·
    refine ⟨355849099174347195760218107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237232732782898130506812071 355849099174347195760218107)
    ·
      refine ⟨533773648761520793640327161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355849099174347195760218107 533773648761520793640327161)
      ·
        refine ⟨400330236571140595230245371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533773648761520793640327161 400330236571140595230245371)
        ·
          refine ⟨600495354856710892845368057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400330236571140595230245371 600495354856710892845368057)
          ·
            refine ⟨450371516142533169634026043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600495354856710892845368057 450371516142533169634026043)
            ·
              refine ⟨675557274213799754451039065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450371516142533169634026043 675557274213799754451039065)
              ·
                refine ⟨506667955660349815838279299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675557274213799754451039065 506667955660349815838279299)
                ·
                  refine ⟨760001933490524723757418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506667955660349815838279299 760001933490524723757418949)
                  ·
                    refine ⟨142500362529473385704516053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760001933490524723757418949 142500362529473385704516053)
                    ·
                      refine ⟨3339852246784532477449595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142500362529473385704516053 3339852246784532477449595)
                      ·
                        rfl

theorem cell23_6504339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_6504339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504339 prefixEnd_6504339 := by exact prefixLift 6504339
  have htrace : WordTrace (prefixWord ++ tailWord_6504339) baseStart_6504339 baseEnd_6504339 := by
    simpa [prefixWord, tailWord_6504339, baseEnd_6504339] using wordTrace_append hprefix tailTrace_6504339
  have hstable : (prefixWord ++ tailWord_6504339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504339).length < 2 ^ (prefixWord ++ tailWord_6504339).sum := by decide
  have hdescent : baseEnd_6504339 < baseStart_6504339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504340 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_6504340 : Nat := 118140960795 + 6504340 * 2 ^ 59
def prefixEnd_6504340 : Nat := 4983230072969 + 3 ^ 40 * 6504340 * 2
def baseEnd_6504340 : Nat := 3339852760265186973537091

theorem tailTrace_6504340 : CollatzResearch.WordTrace tailWord_6504340 prefixEnd_6504340 3339852760265186973537091 := by
  unfold tailWord_6504340
  simp only [CollatzResearch.WordTrace]
  refine ⟨118616384627947253838799237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158155179503929671785065649 118616384627947253838799237)
  ·
    refine ⟨22240572117740110094774857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118616384627947253838799237 22240572117740110094774857)
    ·
      refine ⟨16680429088305082571081143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22240572117740110094774857 16680429088305082571081143)
      ·
        refine ⟨25020643632457623856621715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16680429088305082571081143 25020643632457623856621715)
        ·
          refine ⟨37530965448686435784932573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25020643632457623856621715 37530965448686435784932573)
          ·
            refine ⟨14074112043257413419349715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37530965448686435784932573 14074112043257413419349715)
            ·
              refine ⟨21111168064886120129024573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074112043257413419349715 21111168064886120129024573)
              ·
                refine ⟨7916688024332295048384215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21111168064886120129024573 7916688024332295048384215)
                ·
                  refine ⟨11875032036498442572576323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916688024332295048384215 11875032036498442572576323)
                  ·
                    refine ⟨17812548054747663858864485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11875032036498442572576323 17812548054747663858864485)
                    ·
                      refine ⟨3339852760265186973537091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17812548054747663858864485 3339852760265186973537091)
                      ·
                        rfl

theorem cell23_6504340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_6504340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504340 prefixEnd_6504340 := by exact prefixLift 6504340
  have htrace : WordTrace (prefixWord ++ tailWord_6504340) baseStart_6504340 baseEnd_6504340 := by
    simpa [prefixWord, tailWord_6504340, baseEnd_6504340] using wordTrace_append hprefix tailTrace_6504340
  have hstable : (prefixWord ++ tailWord_6504340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504340).length < 2 ^ (prefixWord ++ tailWord_6504340).sum := by decide
  have hdescent : baseEnd_6504340 < baseStart_6504340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504346 : List Nat := [3, 1, 1, 4, 2, 2, 10]
def baseStart_6504346 : Nat := 118140960795 + 6504346 * 2 ^ 59
def prefixEnd_6504346 : Nat := 4983230072969 + 3 ^ 40 * 6504346 * 2
def baseEnd_6504346 : Nat := 41232788162334740124223

theorem tailTrace_6504346 : CollatzResearch.WordTrace tailWord_6504346 prefixEnd_6504346 41232788162334740124223 := by
  unfold tailWord_6504346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59308247023468192675579223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158155325395915180468211261 59308247023468192675579223)
  ·
    refine ⟨88962370535202289013368835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59308247023468192675579223 88962370535202289013368835)
    ·
      refine ⟨133443555802803433520053253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88962370535202289013368835 133443555802803433520053253)
      ·
        refine ⟨25020666713025643785009985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133443555802803433520053253 25020666713025643785009985)
        ·
          refine ⟨18765500034769232838757489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25020666713025643785009985 18765500034769232838757489)
          ·
            refine ⟨14074125026076924629068117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18765500034769232838757489 14074125026076924629068117)
            ·
              refine ⟨41232788162334740124223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14074125026076924629068117 41232788162334740124223)
              ·
                rfl

theorem cell23_6504346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 10].length) (baseStart_6504346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504346 prefixEnd_6504346 := by exact prefixLift 6504346
  have htrace : WordTrace (prefixWord ++ tailWord_6504346) baseStart_6504346 baseEnd_6504346 := by
    simpa [prefixWord, tailWord_6504346, baseEnd_6504346] using wordTrace_append hprefix tailTrace_6504346
  have hstable : (prefixWord ++ tailWord_6504346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504346).length < 2 ^ (prefixWord ++ tailWord_6504346).sum := by decide
  have hdescent : baseEnd_6504346 < baseStart_6504346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504400 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2]
def baseStart_6504400 : Nat := 118140960795 + 6504400 * 2 ^ 59
def prefixEnd_6504400 : Nat := 4983230072969 + 3 ^ 40 * 6504400 * 2
def baseEnd_6504400 : Nat := 3339883569104456738786815

theorem tailTrace_6504400 : CollatzResearch.WordTrace tailWord_6504400 prefixEnd_6504400 3339883569104456738786815 := by
  unfold tailWord_6504400
  simp only [CollatzResearch.WordTrace]
  refine ⟨118617478817838568962391327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158156638423784758616521769 118617478817838568962391327)
  ·
    refine ⟨177926218226757853443586991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118617478817838568962391327 177926218226757853443586991)
    ·
      refine ⟨266889327340136780165380487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177926218226757853443586991 266889327340136780165380487)
      ·
        refine ⟨400333991010205170248070731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266889327340136780165380487 400333991010205170248070731)
        ·
          refine ⟨600500986515307755372106097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400333991010205170248070731 600500986515307755372106097)
          ·
            refine ⟨450375739886480816529079573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600500986515307755372106097 450375739886480816529079573)
            ·
              refine ⟨21111362807178788274800605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 450375739886480816529079573 21111362807178788274800605)
              ·
                refine ⟨7916761052692045603050227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21111362807178788274800605 7916761052692045603050227)
                ·
                  refine ⟨11875141579038068404575341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7916761052692045603050227 11875141579038068404575341)
                  ·
                    refine ⟨4453178092139275651715753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11875141579038068404575341 4453178092139275651715753)
                    ·
                      refine ⟨3339883569104456738786815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453178092139275651715753 3339883569104456738786815)
                      ·
                        rfl

theorem cell23_6504400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2].length) (baseStart_6504400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504400 prefixEnd_6504400 := by exact prefixLift 6504400
  have htrace : WordTrace (prefixWord ++ tailWord_6504400) baseStart_6504400 baseEnd_6504400 := by
    simpa [prefixWord, tailWord_6504400, baseEnd_6504400] using wordTrace_append hprefix tailTrace_6504400
  have hstable : (prefixWord ++ tailWord_6504400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504400).length < 2 ^ (prefixWord ++ tailWord_6504400).sum := by decide
  have hdescent : baseEnd_6504400 < baseStart_6504400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504540 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_6504540 : Nat := 118140960795 + 6504540 * 2 ^ 59
def prefixEnd_6504540 : Nat := 4983230072969 + 3 ^ 40 * 6504540 * 2
def baseEnd_6504540 : Nat := 3339955456396086191036171

theorem tailTrace_6504540 : CollatzResearch.WordTrace tailWord_6504540 prefixEnd_6504540 3339955456396086191036171 := by
  unfold tailWord_6504540
  simp only [CollatzResearch.WordTrace]
  refine ⟨118620031927584970917439537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158160042570113294556586049 118620031927584970917439537)
  ·
    refine ⟨88965023945688728188079653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118620031927584970917439537 88965023945688728188079653)
    ·
      refine ⟨16680941989816636535264935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88965023945688728188079653 16680941989816636535264935)
      ·
        refine ⟨25021412984724954802897403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16680941989816636535264935 25021412984724954802897403)
        ·
          refine ⟨37532119477087432204346105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25021412984724954802897403 37532119477087432204346105)
          ·
            refine ⟨28149089607815574153259579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37532119477087432204346105 28149089607815574153259579)
            ·
              refine ⟨42223634411723361229889369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28149089607815574153259579 42223634411723361229889369)
              ·
                refine ⟨31667725808792520922417027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42223634411723361229889369 31667725808792520922417027)
                ·
                  refine ⟨47501588713188781383625541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31667725808792520922417027 47501588713188781383625541)
                  ·
                    refine ⟨8906547883722896509429789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47501588713188781383625541 8906547883722896509429789)
                    ·
                      refine ⟨3339955456396086191036171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906547883722896509429789 3339955456396086191036171)
                      ·
                        rfl

theorem cell23_6504540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_6504540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504540 prefixEnd_6504540 := by exact prefixLift 6504540
  have htrace : WordTrace (prefixWord ++ tailWord_6504540) baseStart_6504540 baseEnd_6504540 := by
    simpa [prefixWord, tailWord_6504540, baseEnd_6504540] using wordTrace_append hprefix tailTrace_6504540
  have hstable : (prefixWord ++ tailWord_6504540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504540).length < 2 ^ (prefixWord ++ tailWord_6504540).sum := by decide
  have hdescent : baseEnd_6504540 < baseStart_6504540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504553 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_6504553 : Nat := 118140960795 + 6504553 * 2 ^ 59
def prefixEnd_6504553 : Nat := 4983230072969 + 3 ^ 40 * 6504553 * 2
def baseEnd_6504553 : Nat := 3339962131644594640173611

theorem tailTrace_6504553 : CollatzResearch.WordTrace tailWord_6504553 prefixEnd_6504553 3339962131644594640173611 := by
  unfold tailWord_6504553
  simp only [CollatzResearch.WordTrace]
  refine ⟨237240538004122845055102313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158160358669415230036734875 237240538004122845055102313)
  ·
    refine ⟨177930403503092133791326735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237240538004122845055102313 177930403503092133791326735)
    ·
      refine ⟨266895605254638200686990103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177930403503092133791326735 266895605254638200686990103)
      ·
        refine ⟨400343407881957301030485155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266895605254638200686990103 400343407881957301030485155)
        ·
          refine ⟨600515111822935951545727733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400343407881957301030485155 600515111822935951545727733)
          ·
            refine ⟨56298291733400245457411975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 600515111822935951545727733 56298291733400245457411975)
            ·
              refine ⟨84447437600100368186117963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56298291733400245457411975 84447437600100368186117963)
              ·
                refine ⟨126671156400150552279176945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84447437600100368186117963 126671156400150552279176945)
                ·
                  refine ⟨95003367300112914209382709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126671156400150552279176945 95003367300112914209382709)
                  ·
                    refine ⟨8906565684385585707129629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95003367300112914209382709 8906565684385585707129629)
                    ·
                      refine ⟨3339962131644594640173611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906565684385585707129629 3339962131644594640173611)
                      ·
                        rfl

theorem cell23_6504553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_6504553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504553 prefixEnd_6504553 := by exact prefixLift 6504553
  have htrace : WordTrace (prefixWord ++ tailWord_6504553) baseStart_6504553 baseEnd_6504553 := by
    simpa [prefixWord, tailWord_6504553, baseEnd_6504553] using wordTrace_append hprefix tailTrace_6504553
  have hstable : (prefixWord ++ tailWord_6504553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504553).length < 2 ^ (prefixWord ++ tailWord_6504553).sum := by decide
  have hdescent : baseEnd_6504553 < baseStart_6504553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504607 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 1, 5]
def baseStart_6504607 : Nat := 118140960795 + 6504607 * 2 ^ 59
def prefixEnd_6504607 : Nat := 4983230072969 + 3 ^ 40 * 6504607 * 2
def baseEnd_6504607 : Nat := 1113329953199979142966121

theorem tailTrace_6504607 : CollatzResearch.WordTrace tailWord_6504607 prefixEnd_6504607 1113329953199979142966121 := by
  unfold tailWord_6504607
  simp only [CollatzResearch.WordTrace]
  refine ⟨237242507545927212277568075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158161671697284808185045383 237242507545927212277568075)
  ·
    refine ⟨355863761318890818416352113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237242507545927212277568075 355863761318890818416352113)
    ·
      refine ⟨266897820989168113812264085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355863761318890818416352113 266897820989168113812264085)
      ·
        refine ⟨12510835358867255334949879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266897820989168113812264085 12510835358867255334949879)
        ·
          refine ⟨18766253038300883002424819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12510835358867255334949879 18766253038300883002424819)
          ·
            refine ⟨28149379557451324503637229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18766253038300883002424819 28149379557451324503637229)
            ·
              refine ⟨10556017334044246688863961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28149379557451324503637229 10556017334044246688863961)
              ·
                refine ⟨7917013000533185016647971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10556017334044246688863961 7917013000533185016647971)
                ·
                  refine ⟨11875519500799777524971957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917013000533185016647971 11875519500799777524971957)
                  ·
                    refine ⟨1113329953199979142966121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11875519500799777524971957 1113329953199979142966121)
                    ·
                      rfl

theorem cell23_6504607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_6504607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504607 prefixEnd_6504607 := by exact prefixLift 6504607
  have htrace : WordTrace (prefixWord ++ tailWord_6504607) baseStart_6504607 baseEnd_6504607 := by
    simpa [prefixWord, tailWord_6504607, baseEnd_6504607] using wordTrace_append hprefix tailTrace_6504607
  have hstable : (prefixWord ++ tailWord_6504607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504607).length < 2 ^ (prefixWord ++ tailWord_6504607).sum := by decide
  have hdescent : baseEnd_6504607 < baseStart_6504607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504661 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6504661 : Nat := 118140960795 + 6504661 * 2 ^ 59
def prefixEnd_6504661 : Nat := 4983230072969 + 3 ^ 40 * 6504661 * 2
def baseEnd_6504661 : Nat := 3340017587555280217623115

theorem tailTrace_6504661 : CollatzResearch.WordTrace tailWord_6504661 prefixEnd_6504661 3340017587555280217623115 := by
  unfold tailWord_6504661
  simp only [CollatzResearch.WordTrace]
  refine ⟨237244477087731579500033837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158162984725154386333355891 237244477087731579500033837)
  ·
    refine ⟨88966678907899342312512689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237244477087731579500033837 88966678907899342312512689)
    ·
      refine ⟨66725009180924506734384517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88966678907899342312512689 66725009180924506734384517)
      ·
        refine ⟨12510939221423345012697097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66725009180924506734384517 12510939221423345012697097)
        ·
          refine ⟨9383204416067508759522823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12510939221423345012697097 9383204416067508759522823)
          ·
            refine ⟨14074806624101263139284235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9383204416067508759522823 14074806624101263139284235)
            ·
              refine ⟨21112209936151894708926353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074806624101263139284235 21112209936151894708926353)
              ·
                refine ⟨15834157452113921031694765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21112209936151894708926353 15834157452113921031694765)
                ·
                  refine ⟨5937809044542720386885537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15834157452113921031694765 5937809044542720386885537)
                  ·
                    refine ⟨4453356783407040290164153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5937809044542720386885537 4453356783407040290164153)
                    ·
                      refine ⟨3340017587555280217623115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453356783407040290164153 3340017587555280217623115)
                      ·
                        rfl

theorem cell23_6504661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6504661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504661 prefixEnd_6504661 := by exact prefixLift 6504661
  have htrace : WordTrace (prefixWord ++ tailWord_6504661) baseStart_6504661 baseEnd_6504661 := by
    simpa [prefixWord, tailWord_6504661, baseEnd_6504661] using wordTrace_append hprefix tailTrace_6504661
  have hstable : (prefixWord ++ tailWord_6504661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504661).length < 2 ^ (prefixWord ++ tailWord_6504661).sum := by decide
  have hdescent : baseEnd_6504661 < baseStart_6504661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504663 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 7]
def baseStart_6504663 : Nat := 118140960795 + 6504663 * 2 ^ 59
def prefixEnd_6504663 : Nat := 4983230072969 + 3 ^ 40 * 6504663 * 2
def baseEnd_6504663 : Nat := 1113339538172196403266035

theorem tailTrace_6504663 : CollatzResearch.WordTrace tailWord_6504663 prefixEnd_6504663 1113339538172196403266035 := by
  unfold tailWord_6504663
  simp only [CollatzResearch.WordTrace]
  refine ⟨237244550033724333841606643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158163033355816222561071095 237244550033724333841606643)
  ·
    refine ⟨355866825050586500762409965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237244550033724333841606643 355866825050586500762409965)
    ·
      refine ⟨133450059393969937785903737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355866825050586500762409965 133450059393969937785903737)
      ·
        refine ⟨100087544545477453339427803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133450059393969937785903737 100087544545477453339427803)
        ·
          refine ⟨150131316818216180009141705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100087544545477453339427803 150131316818216180009141705)
          ·
            refine ⟨112598487613662135006856279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150131316818216180009141705 112598487613662135006856279)
            ·
              refine ⟨168897731420493202510284419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112598487613662135006856279 168897731420493202510284419)
              ·
                refine ⟨253346597130739803765426629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168897731420493202510284419 253346597130739803765426629)
                ·
                  refine ⟨47502486962013713206017493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253346597130739803765426629 47502486962013713206017493)
                  ·
                    refine ⟨1113339538172196403266035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47502486962013713206017493 1113339538172196403266035)
                    ·
                      rfl

theorem cell23_6504663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_6504663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504663 prefixEnd_6504663 := by exact prefixLift 6504663
  have htrace : WordTrace (prefixWord ++ tailWord_6504663) baseStart_6504663 baseEnd_6504663 := by
    simpa [prefixWord, tailWord_6504663, baseEnd_6504663] using wordTrace_append hprefix tailTrace_6504663
  have hstable : (prefixWord ++ tailWord_6504663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504663).length < 2 ^ (prefixWord ++ tailWord_6504663).sum := by decide
  have hdescent : baseEnd_6504663 < baseStart_6504663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504677 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6504677 : Nat := 118140960795 + 6504677 * 2 ^ 59
def prefixEnd_6504677 : Nat := 4983230072969 + 3 ^ 40 * 6504677 * 2
def baseEnd_6504677 : Nat := 3340025803245752155023041

theorem tailTrace_6504677 : CollatzResearch.WordTrace tailWord_6504677 prefixEnd_6504677 3340025803245752155023041 := by
  unfold tailWord_6504677
  simp only [CollatzResearch.WordTrace]
  refine ⟨237245060655673614232616285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158163373770449076155077523 237245060655673614232616285)
  ·
    refine ⟨88966897745877605337231107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237245060655673614232616285 88966897745877605337231107)
    ·
      refine ⟨133450346618816408005846661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88966897745877605337231107 133450346618816408005846661)
      ·
        refine ⟨25021939991028076501096249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133450346618816408005846661 25021939991028076501096249)
        ·
          refine ⟨18766454993271057375822187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25021939991028076501096249 18766454993271057375822187)
          ·
            refine ⟨28149682489906586063733281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18766454993271057375822187 28149682489906586063733281)
            ·
              refine ⟨21112261867429939547799961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28149682489906586063733281 21112261867429939547799961)
              ·
                refine ⟨15834196400572454660849971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21112261867429939547799961 15834196400572454660849971)
                ·
                  refine ⟨23751294600858681991274957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15834196400572454660849971 23751294600858681991274957)
                  ·
                    refine ⟨8906735475322005746728109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23751294600858681991274957 8906735475322005746728109)
                    ·
                      refine ⟨3340025803245752155023041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906735475322005746728109 3340025803245752155023041)
                      ·
                        rfl

theorem cell23_6504677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6504677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504677 prefixEnd_6504677 := by exact prefixLift 6504677
  have htrace : WordTrace (prefixWord ++ tailWord_6504677) baseStart_6504677 baseEnd_6504677 := by
    simpa [prefixWord, tailWord_6504677, baseEnd_6504677] using wordTrace_append hprefix tailTrace_6504677
  have hstable : (prefixWord ++ tailWord_6504677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504677).length < 2 ^ (prefixWord ++ tailWord_6504677).sum := by decide
  have hdescent : baseEnd_6504677 < baseStart_6504677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504711 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6504711 : Nat := 118140960795 + 6504711 * 2 ^ 59
def prefixEnd_6504711 : Nat := 4983230072969 + 3 ^ 40 * 6504711 * 2
def baseEnd_6504711 : Nat := 3340043261588005021997885

theorem tailTrace_6504711 : CollatzResearch.WordTrace tailWord_6504711 prefixEnd_6504711 3340043261588005021997885 := by
  unfold tailWord_6504711
  simp only [CollatzResearch.WordTrace]
  refine ⟨237246300737550438039353987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158164200491700292026235991 237246300737550438039353987)
  ·
    refine ⟨355869451106325657059030981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237246300737550438039353987 355869451106325657059030981)
    ·
      refine ⟨66725522082436060698568309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355869451106325657059030981 66725522082436060698568309)
      ·
        refine ⟨6255517695228380690490779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66725522082436060698568309 6255517695228380690490779)
        ·
          refine ⟨9383276542842571035736169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255517695228380690490779 9383276542842571035736169)
          ·
            refine ⟨7037457407131928276802127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383276542842571035736169 7037457407131928276802127)
            ·
              refine ⟨10556186110697892415203191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037457407131928276802127 10556186110697892415203191)
              ·
                refine ⟨15834279166046838622804787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556186110697892415203191 15834279166046838622804787)
                ·
                  refine ⟨23751418749070257934207181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15834279166046838622804787 23751418749070257934207181)
                  ·
                    refine ⟨8906782030901346725327693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23751418749070257934207181 8906782030901346725327693)
                    ·
                      refine ⟨3340043261588005021997885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906782030901346725327693 3340043261588005021997885)
                      ·
                        rfl

theorem cell23_6504711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6504711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504711 prefixEnd_6504711 := by exact prefixLift 6504711
  have htrace : WordTrace (prefixWord ++ tailWord_6504711) baseStart_6504711 baseEnd_6504711 := by
    simpa [prefixWord, tailWord_6504711, baseEnd_6504711] using wordTrace_append hprefix tailTrace_6504711
  have hstable : (prefixWord ++ tailWord_6504711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504711).length < 2 ^ (prefixWord ++ tailWord_6504711).sum := by decide
  have hdescent : baseEnd_6504711 < baseStart_6504711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504780 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6504780 : Nat := 118140960795 + 6504780 * 2 ^ 59
def prefixEnd_6504780 : Nat := 4983230072969 + 3 ^ 40 * 6504780 * 2
def baseEnd_6504780 : Nat := 3340078691753165252035067

theorem tailTrace_6504780 : CollatzResearch.WordTrace tailWord_6504780 prefixEnd_6504780 3340078691753165252035067 := by
  unfold tailWord_6504780
  simp only [CollatzResearch.WordTrace]
  refine ⟨118624408687150231411807897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158165878249533641882410529 118624408687150231411807897)
  ·
    refine ⟨88968306515362673558855923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118624408687150231411807897 88968306515362673558855923)
    ·
      refine ⟨133452459773044010338283885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88968306515362673558855923 133452459773044010338283885)
      ·
        refine ⟨50044672414891503876856457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133452459773044010338283885 50044672414891503876856457)
        ·
          refine ⟨37533504311168627907642343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50044672414891503876856457 37533504311168627907642343)
          ·
            refine ⟨56300256466752941861463515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37533504311168627907642343 56300256466752941861463515)
            ·
              refine ⟨84450384700129412792195273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56300256466752941861463515 84450384700129412792195273)
              ·
                refine ⟨63337788525097059594146455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84450384700129412792195273 63337788525097059594146455)
                ·
                  refine ⟨95006682787645589391219683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63337788525097059594146455 95006682787645589391219683)
                  ·
                    refine ⟨142510024181468384086829525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95006682787645589391219683 142510024181468384086829525)
                    ·
                      refine ⟨3340078691753165252035067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142510024181468384086829525 3340078691753165252035067)
                      ·
                        rfl

theorem cell23_6504780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6504780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504780 prefixEnd_6504780 := by exact prefixLift 6504780
  have htrace : WordTrace (prefixWord ++ tailWord_6504780) baseStart_6504780 baseEnd_6504780 := by
    simpa [prefixWord, tailWord_6504780, baseEnd_6504780] using wordTrace_append hprefix tailTrace_6504780
  have hstable : (prefixWord ++ tailWord_6504780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504780).length < 2 ^ (prefixWord ++ tailWord_6504780).sum := by decide
  have hdescent : baseEnd_6504780 < baseStart_6504780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504817 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_6504817 : Nat := 118140960795 + 6504817 * 2 ^ 59
def prefixEnd_6504817 : Nat := 4983230072969 + 3 ^ 40 * 6504817 * 2
def baseEnd_6504817 : Nat := 1113365896845793869090799

theorem tailTrace_6504817 : CollatzResearch.WordTrace tailWord_6504817 prefixEnd_6504817 1113365896845793869090799 := by
  unfold tailWord_6504817
  simp only [CollatzResearch.WordTrace]
  refine ⟨237250166875166418142712705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158166777916777612095141803 237250166875166418142712705)
  ·
    refine ⟨177937625156374813607034529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237250166875166418142712705 177937625156374813607034529)
    ·
      refine ⟨133453218867281110205275897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177937625156374813607034529 133453218867281110205275897)
      ·
        refine ⟨100089914150460832653956923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133453218867281110205275897 100089914150460832653956923)
        ·
          refine ⟨150134871225691248980935385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100089914150460832653956923 150134871225691248980935385)
          ·
            refine ⟨112601153419268436735701539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150134871225691248980935385 112601153419268436735701539)
            ·
              refine ⟨168901730128902655103552309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112601153419268436735701539 168901730128902655103552309)
              ·
                refine ⟨15834537199584623915958029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168901730128902655103552309 15834537199584623915958029)
                ·
                  refine ⟨5937951449844233968484261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15834537199584623915958029 5937951449844233968484261)
                  ·
                    refine ⟨1113365896845793869090799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5937951449844233968484261 1113365896845793869090799)
                    ·
                      rfl

theorem cell23_6504817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_6504817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504817 prefixEnd_6504817 := by exact prefixLift 6504817
  have htrace : WordTrace (prefixWord ++ tailWord_6504817) baseStart_6504817 baseEnd_6504817 := by
    simpa [prefixWord, tailWord_6504817, baseEnd_6504817] using wordTrace_append hprefix tailTrace_6504817
  have hstable : (prefixWord ++ tailWord_6504817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504817).length < 2 ^ (prefixWord ++ tailWord_6504817).sum := by decide
  have hdescent : baseEnd_6504817 < baseStart_6504817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504844 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_6504844 : Nat := 118140960795 + 6504844 * 2 ^ 59
def prefixEnd_6504844 : Nat := 4983230072969 + 3 ^ 40 * 6504844 * 2
def baseEnd_6504844 : Nat := 3340111554515053001634773

theorem tailTrace_6504844 : CollatzResearch.WordTrace tailWord_6504844 prefixEnd_6504844 3340111554515053001634773 := by
  unfold tailWord_6504844
  simp only [CollatzResearch.WordTrace]
  refine ⟨118625575823034300876972793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158167434430712401169297057 118625575823034300876972793)
  ·
    refine ⟨88969181867275725657729595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118625575823034300876972793 88969181867275725657729595)
    ·
      refine ⟨133453772800913588486594393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88969181867275725657729595 133453772800913588486594393)
      ·
        refine ⟨100090329600685191364945795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133453772800913588486594393 100090329600685191364945795)
        ·
          refine ⟨150135494401027787047418693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100090329600685191364945795 150135494401027787047418693)
          ·
            refine ⟨28150405200192710071391005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150135494401027787047418693 28150405200192710071391005)
            ·
              refine ⟨10556401950072266276771627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28150405200192710071391005 10556401950072266276771627)
              ·
                refine ⟨15834602925108399415157441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556401950072266276771627 15834602925108399415157441)
                ·
                  refine ⟨11875952193831299561368081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15834602925108399415157441 11875952193831299561368081)
                  ·
                    refine ⟨8906964145373474671026061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11875952193831299561368081 8906964145373474671026061)
                    ·
                      refine ⟨3340111554515053001634773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8906964145373474671026061 3340111554515053001634773)
                      ·
                        rfl

theorem cell23_6504844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_6504844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504844 prefixEnd_6504844 := by exact prefixLift 6504844
  have htrace : WordTrace (prefixWord ++ tailWord_6504844) baseStart_6504844 baseEnd_6504844 := by
    simpa [prefixWord, tailWord_6504844, baseEnd_6504844] using wordTrace_append hprefix tailTrace_6504844
  have hstable : (prefixWord ++ tailWord_6504844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504844).length < 2 ^ (prefixWord ++ tailWord_6504844).sum := by decide
  have hdescent : baseEnd_6504844 < baseStart_6504844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504864 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 6]
def baseStart_6504864 : Nat := 118140960795 + 6504864 * 2 ^ 59
def prefixEnd_6504864 : Nat := 4983230072969 + 3 ^ 40 * 6504864 * 2
def baseEnd_6504864 : Nat := 371124647125349213709409

theorem tailTrace_6504864 : CollatzResearch.WordTrace tailWord_6504864 prefixEnd_6504864 371124647125349213709409 := by
  unfold tailWord_6504864
  simp only [CollatzResearch.WordTrace]
  refine ⟨118625940552998072584836823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158167920737330763446449097 118625940552998072584836823)
  ·
    refine ⟨177938910829497108877255235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118625940552998072584836823 177938910829497108877255235)
    ·
      refine ⟨266908366244245663315882853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177938910829497108877255235 266908366244245663315882853)
      ·
        refine ⟨50045318670796061871728035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266908366244245663315882853 50045318670796061871728035)
        ·
          refine ⟨75067978006194092807592053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50045318670796061871728035 75067978006194092807592053)
          ·
            refine ⟨7037622938080696200711755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75067978006194092807592053 7037622938080696200711755)
            ·
              refine ⟨10556434407121044301067633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037622938080696200711755 10556434407121044301067633)
              ·
                refine ⟨7917325805340783225800725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10556434407121044301067633 7917325805340783225800725)
                ·
                  refine ⟨371124647125349213709409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7917325805340783225800725 371124647125349213709409)
                  ·
                    rfl

theorem cell23_6504864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_6504864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504864 prefixEnd_6504864 := by exact prefixLift 6504864
  have htrace : WordTrace (prefixWord ++ tailWord_6504864) baseStart_6504864 baseEnd_6504864 := by
    simpa [prefixWord, tailWord_6504864, baseEnd_6504864] using wordTrace_append hprefix tailTrace_6504864
  have hstable : (prefixWord ++ tailWord_6504864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504864).length < 2 ^ (prefixWord ++ tailWord_6504864).sum := by decide
  have hdescent : baseEnd_6504864 < baseStart_6504864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504894 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_6504894 : Nat := 118140960795 + 6504894 * 2 ^ 59
def prefixEnd_6504894 : Nat := 4983230072969 + 3 ^ 40 * 6504894 * 2
def baseEnd_6504894 : Nat := 1113379076182592602003181

theorem tailTrace_6504894 : CollatzResearch.WordTrace tailWord_6504894 prefixEnd_6504894 1113379076182592602003181 := by
  unfold tailWord_6504894
  simp only [CollatzResearch.WordTrace]
  refine ⟨29656621911985932536658217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158168650197258306862177157 29656621911985932536658217)
  ·
    refine ⟨22242466433989449402493663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29656621911985932536658217 22242466433989449402493663)
    ·
      refine ⟨33363699650984174103740495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242466433989449402493663 33363699650984174103740495)
      ·
        refine ⟨50045549476476261155610743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33363699650984174103740495 50045549476476261155610743)
        ·
          refine ⟨75068324214714391733416115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50045549476476261155610743 75068324214714391733416115)
          ·
            refine ⟨112602486322071587600124173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75068324214714391733416115 112602486322071587600124173)
            ·
              refine ⟨42225932370776845350046565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112602486322071587600124173 42225932370776845350046565)
              ·
                refine ⟨7917362319520658503133731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42225932370776845350046565 7917362319520658503133731)
                ·
                  refine ⟨11876043479280987754700597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917362319520658503133731 11876043479280987754700597)
                  ·
                    refine ⟨1113379076182592602003181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11876043479280987754700597 1113379076182592602003181)
                    ·
                      rfl

theorem cell23_6504894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_6504894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504894 prefixEnd_6504894 := by exact prefixLift 6504894
  have htrace : WordTrace (prefixWord ++ tailWord_6504894) baseStart_6504894 baseEnd_6504894 := by
    simpa [prefixWord, tailWord_6504894, baseEnd_6504894] using wordTrace_append hprefix tailTrace_6504894
  have hstable : (prefixWord ++ tailWord_6504894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504894).length < 2 ^ (prefixWord ++ tailWord_6504894).sum := by decide
  have hdescent : baseEnd_6504894 < baseStart_6504894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504918 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6504918 : Nat := 118140960795 + 6504918 * 2 ^ 59
def prefixEnd_6504918 : Nat := 4983230072969 + 3 ^ 40 * 6504918 * 2
def baseEnd_6504918 : Nat := 3340149552083485712109433

theorem tailTrace_6504918 : CollatzResearch.WordTrace tailWord_6504918 prefixEnd_6504918 3340149552083485712109433 := by
  unfold tailWord_6504918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828365665487532024508713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158169233765200341594759605 14828365665487532024508713)
  ·
    refine ⟨11121274249115649018381535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14828365665487532024508713 11121274249115649018381535)
    ·
      refine ⟨16681911373673473527572303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11121274249115649018381535 16681911373673473527572303)
      ·
        refine ⟨25022867060510210291358455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16681911373673473527572303 25022867060510210291358455)
        ·
          refine ⟨37534300590765315437037683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25022867060510210291358455 37534300590765315437037683)
          ·
            refine ⟨56301450886147973155556525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37534300590765315437037683 56301450886147973155556525)
            ·
              refine ⟨21113044082305489933333697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56301450886147973155556525 21113044082305489933333697)
              ·
                refine ⟨15834783061729117450000273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21113044082305489933333697 15834783061729117450000273)
                ·
                  refine ⟨11876087296296838087500205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15834783061729117450000273 11876087296296838087500205)
                  ·
                    refine ⟨4453532736111314282812577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11876087296296838087500205 4453532736111314282812577)
                    ·
                      refine ⟨3340149552083485712109433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453532736111314282812577 3340149552083485712109433)
                      ·
                        rfl

theorem cell23_6504918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6504918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504918 prefixEnd_6504918 := by exact prefixLift 6504918
  have htrace : WordTrace (prefixWord ++ tailWord_6504918) baseStart_6504918 baseEnd_6504918 := by
    simpa [prefixWord, tailWord_6504918, baseEnd_6504918] using wordTrace_append hprefix tailTrace_6504918
  have hstable : (prefixWord ++ tailWord_6504918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504918).length < 2 ^ (prefixWord ++ tailWord_6504918).sum := by decide
  have hdescent : baseEnd_6504918 < baseStart_6504918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504925 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_6504925 : Nat := 118140960795 + 6504925 * 2 ^ 59
def prefixEnd_6504925 : Nat := 4983230072969 + 3 ^ 40 * 6504925 * 2
def baseEnd_6504925 : Nat := 3340153146448067184721901

theorem tailTrace_6504925 : CollatzResearch.WordTrace tailWord_6504925 prefixEnd_6504925 3340153146448067184721901 := by
  unfold tailWord_6504925
  simp only [CollatzResearch.WordTrace]
  refine ⟨237254105958775152587644229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158169403972516768391762819 237254105958775152587644229)
  ·
    refine ⟨44485144867270341110183293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237254105958775152587644229 44485144867270341110183293)
    ·
      refine ⟨16681929325226377916318735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44485144867270341110183293 16681929325226377916318735)
      ·
        refine ⟨25022893987839566874478103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16681929325226377916318735 25022893987839566874478103)
        ·
          refine ⟨37534340981759350311717155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25022893987839566874478103 37534340981759350311717155)
          ·
            refine ⟨56301511472639025467575733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37534340981759350311717155 56301511472639025467575733)
            ·
              refine ⟨5278266700559908637585225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56301511472639025467575733 5278266700559908637585225)
              ·
                refine ⟨3958700025419931478188919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278266700559908637585225 3958700025419931478188919)
                ·
                  refine ⟨5938050038129897217283379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958700025419931478188919 5938050038129897217283379)
                  ·
                    refine ⟨8907075057194845825925069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5938050038129897217283379 8907075057194845825925069)
                    ·
                      refine ⟨3340153146448067184721901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907075057194845825925069 3340153146448067184721901)
                      ·
                        rfl

theorem cell23_6504925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_6504925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504925 prefixEnd_6504925 := by exact prefixLift 6504925
  have htrace : WordTrace (prefixWord ++ tailWord_6504925) baseStart_6504925 baseEnd_6504925 := by
    simpa [prefixWord, tailWord_6504925, baseEnd_6504925] using wordTrace_append hprefix tailTrace_6504925
  have hstable : (prefixWord ++ tailWord_6504925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504925).length < 2 ^ (prefixWord ++ tailWord_6504925).sum := by decide
  have hdescent : baseEnd_6504925 < baseStart_6504925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504927 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_6504927 : Nat := 118140960795 + 6504927 * 2 ^ 59
def prefixEnd_6504927 : Nat := 4983230072969 + 3 ^ 40 * 6504927 * 2
def baseEnd_6504927 : Nat := 3340154173409376176896891

theorem tailTrace_6504927 : CollatzResearch.WordTrace tailWord_6504927 prefixEnd_6504927 3340154173409376176896891 := by
  unfold tailWord_6504927
  simp only [CollatzResearch.WordTrace]
  refine ⟨237254178904767906929217035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158169452603178604619478023 237254178904767906929217035)
  ·
    refine ⟨355881268357151860393825553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237254178904767906929217035 355881268357151860393825553)
    ·
      refine ⟨266910951267863895295369165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355881268357151860393825553 266910951267863895295369165)
      ·
        refine ⟨100091606725448960735763437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266910951267863895295369165 100091606725448960735763437)
        ·
          refine ⟨37534352522043360275911289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100091606725448960735763437 37534352522043360275911289)
          ·
            refine ⟨28150764391532520206933467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37534352522043360275911289 28150764391532520206933467)
            ·
              refine ⟨42226146587298780310400201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28150764391532520206933467 42226146587298780310400201)
              ·
                refine ⟨31669609940474085232800151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42226146587298780310400201 31669609940474085232800151)
                ·
                  refine ⟨47504414910711127849200227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31669609940474085232800151 47504414910711127849200227)
                  ·
                    refine ⟨71256622366066691773800341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47504414910711127849200227 71256622366066691773800341)
                    ·
                      refine ⟨3340154173409376176896891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71256622366066691773800341 3340154173409376176896891)
                      ·
                        rfl

theorem cell23_6504927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_6504927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504927 prefixEnd_6504927 := by exact prefixLift 6504927
  have htrace : WordTrace (prefixWord ++ tailWord_6504927) baseStart_6504927 baseEnd_6504927 := by
    simpa [prefixWord, tailWord_6504927, baseEnd_6504927] using wordTrace_append hprefix tailTrace_6504927
  have hstable : (prefixWord ++ tailWord_6504927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504927).length < 2 ^ (prefixWord ++ tailWord_6504927).sum := by decide
  have hdescent : baseEnd_6504927 < baseStart_6504927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6504997 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_6504997 : Nat := 118140960795 + 6504997 * 2 ^ 59
def prefixEnd_6504997 : Nat := 4983230072969 + 3 ^ 40 * 6504997 * 2
def baseEnd_6504997 : Nat := 1113396705685063634340523

theorem tailTrace_6504997 : CollatzResearch.WordTrace tailWord_6504997 prefixEnd_6504997 1113396705685063634340523 := by
  unfold tailWord_6504997
  simp only [CollatzResearch.WordTrace]
  refine ⟨237256732014514308884265245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158171154676342872589510163 237256732014514308884265245)
  ·
    refine ⟨88971274505442865831599467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237256732014514308884265245 88971274505442865831599467)
    ·
      refine ⟨133456911758164298747399201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88971274505442865831599467 133456911758164298747399201)
      ·
        refine ⟨100092683818623224060549401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133456911758164298747399201 100092683818623224060549401)
        ·
          refine ⟨75069512863967418045412051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100092683818623224060549401 75069512863967418045412051)
          ·
            refine ⟨112604269295951127068118077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75069512863967418045412051 112604269295951127068118077)
            ·
              refine ⟨42226600985981672650544279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112604269295951127068118077 42226600985981672650544279)
              ·
                refine ⟨63339901478972508975816419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42226600985981672650544279 63339901478972508975816419)
                ·
                  refine ⟨95009852218458763463724629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63339901478972508975816419 95009852218458763463724629)
                  ·
                    refine ⟨1113396705685063634340523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95009852218458763463724629 1113396705685063634340523)
                    ·
                      rfl

theorem cell23_6504997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_6504997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6504997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6504997 prefixEnd_6504997 := by exact prefixLift 6504997
  have htrace : WordTrace (prefixWord ++ tailWord_6504997) baseStart_6504997 baseEnd_6504997 := by
    simpa [prefixWord, tailWord_6504997, baseEnd_6504997] using wordTrace_append hprefix tailTrace_6504997
  have hstable : (prefixWord ++ tailWord_6504997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6504997).length < 2 ^ (prefixWord ++ tailWord_6504997).sum := by decide
  have hdescent : baseEnd_6504997 < baseStart_6504997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6504997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505005 : List Nat := [1, 5, 4, 1, 1, 1, 3, 7]
def baseStart_6505005 : Nat := 118140960795 + 6505005 * 2 ^ 59
def prefixEnd_6505005 : Nat := 4983230072969 + 3 ^ 40 * 6505005 * 2
def baseEnd_6505005 : Nat := 123710897218534328582279

theorem tailTrace_6505005 : CollatzResearch.WordTrace tailWord_6505005 prefixEnd_6505005 123710897218534328582279 := by
  unfold tailWord_6505005
  simp only [CollatzResearch.WordTrace]
  refine ⟨237257023798485326250556469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158171349198990217500370979 237257023798485326250556469)
  ·
    refine ⟨22242845981107999335989669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237257023798485326250556469 22242845981107999335989669)
    ·
      refine ⟨4170533621457749875498063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22242845981107999335989669 4170533621457749875498063)
      ·
        refine ⟨6255800432186624813247095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170533621457749875498063 6255800432186624813247095)
        ·
          refine ⟨9383700648279937219870643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255800432186624813247095 9383700648279937219870643)
          ·
            refine ⟨14075550972419905829805965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9383700648279937219870643 14075550972419905829805965)
            ·
              refine ⟨5278331614657464686177237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14075550972419905829805965 5278331614657464686177237)
              ·
                refine ⟨123710897218534328582279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5278331614657464686177237 123710897218534328582279)
                ·
                  rfl

theorem cell23_6505005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 7].length) (baseStart_6505005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505005 prefixEnd_6505005 := by exact prefixLift 6505005
  have htrace : WordTrace (prefixWord ++ tailWord_6505005) baseStart_6505005 baseEnd_6505005 := by
    simpa [prefixWord, tailWord_6505005, baseEnd_6505005] using wordTrace_append hprefix tailTrace_6505005
  have hstable : (prefixWord ++ tailWord_6505005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505005).length < 2 ^ (prefixWord ++ tailWord_6505005).sum := by decide
  have hdescent : baseEnd_6505005 < baseStart_6505005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505025 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6505025 : Nat := 118140960795 + 6505025 * 2 ^ 59
def prefixEnd_6505025 : Nat := 4983230072969 + 3 ^ 40 * 6505025 * 2
def baseEnd_6505025 : Nat := 3340204494513516793471441

theorem tailTrace_6505025 : CollatzResearch.WordTrace tailWord_6505025 prefixEnd_6505025 3340204494513516793471441 := by
  unfold tailWord_6505025
  simp only [CollatzResearch.WordTrace]
  refine ⟨237257753258412869666284529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158171835505608579777523019 237257753258412869666284529)
  ·
    refine ⟨177943314943809652249713397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237257753258412869666284529 177943314943809652249713397)
    ·
      refine ⟨16682185775982154898410631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177943314943809652249713397 16682185775982154898410631)
      ·
        refine ⟨25023278663973232347615947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16682185775982154898410631 25023278663973232347615947)
        ·
          refine ⟨37534917995959848521423921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25023278663973232347615947 37534917995959848521423921)
          ·
            refine ⟨28151188496969886391067941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37534917995959848521423921 28151188496969886391067941)
            ·
              refine ⟨5278347843181853698325239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28151188496969886391067941 5278347843181853698325239)
              ·
                refine ⟨7917521764772780547487859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278347843181853698325239 7917521764772780547487859)
                ·
                  refine ⟨11876282647159170821231789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917521764772780547487859 11876282647159170821231789)
                  ·
                    refine ⟨4453605992684689057961921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11876282647159170821231789 4453605992684689057961921)
                    ·
                      refine ⟨3340204494513516793471441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453605992684689057961921 3340204494513516793471441)
                      ·
                        rfl

theorem cell23_6505025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6505025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505025 prefixEnd_6505025 := by exact prefixLift 6505025
  have htrace : WordTrace (prefixWord ++ tailWord_6505025) baseStart_6505025 baseEnd_6505025 := by
    simpa [prefixWord, tailWord_6505025, baseEnd_6505025] using wordTrace_append hprefix tailTrace_6505025
  have hstable : (prefixWord ++ tailWord_6505025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505025).length < 2 ^ (prefixWord ++ tailWord_6505025).sum := by decide
  have hdescent : baseEnd_6505025 < baseStart_6505025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505034 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_6505034 : Nat := 118140960795 + 6505034 * 2 ^ 59
def prefixEnd_6505034 : Nat := 4983230072969 + 3 ^ 40 * 6505034 * 2
def baseEnd_6505034 : Nat := 3340209115839407258258899

theorem tailTrace_6505034 : CollatzResearch.WordTrace tailWord_6505034 prefixEnd_6505034 3340209115839407258258899 := by
  unfold tailWord_6505034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59314520378845066050840539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158172054343586842802241437 59314520378845066050840539)
  ·
    refine ⟨88971780568267599076260809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59314520378845066050840539 88971780568267599076260809)
    ·
      refine ⟨66728835426200699307195607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88971780568267599076260809 66728835426200699307195607)
      ·
        refine ⟨100093253139301048960793411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66728835426200699307195607 100093253139301048960793411)
        ·
          refine ⟨150139879708951573441190117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100093253139301048960793411 150139879708951573441190117)
          ·
            refine ⟨28151227445428420020223147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150139879708951573441190117 28151227445428420020223147)
            ·
              refine ⟨42226841168142630030334721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28151227445428420020223147 42226841168142630030334721)
              ·
                refine ⟨31670130876106972522751041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42226841168142630030334721 31670130876106972522751041)
                ·
                  refine ⟨23752598157080229392063281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31670130876106972522751041 23752598157080229392063281)
                  ·
                    refine ⟨17814448617810172044047461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23752598157080229392063281 17814448617810172044047461)
                    ·
                      refine ⟨3340209115839407258258899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17814448617810172044047461 3340209115839407258258899)
                      ·
                        rfl

theorem cell23_6505034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_6505034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505034 prefixEnd_6505034 := by exact prefixLift 6505034
  have htrace : WordTrace (prefixWord ++ tailWord_6505034) baseStart_6505034 baseEnd_6505034 := by
    simpa [prefixWord, tailWord_6505034, baseEnd_6505034] using wordTrace_append hprefix tailTrace_6505034
  have hstable : (prefixWord ++ tailWord_6505034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505034).length < 2 ^ (prefixWord ++ tailWord_6505034).sum := by decide
  have hdescent : baseEnd_6505034 < baseStart_6505034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505044 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6505044 : Nat := 118140960795 + 6505044 * 2 ^ 59
def prefixEnd_6505044 : Nat := 4983230072969 + 3 ^ 40 * 6505044 * 2
def baseEnd_6505044 : Nat := 371134916738439135459317

theorem tailTrace_6505044 : CollatzResearch.WordTrace tailWord_6505044 prefixEnd_6505044 371134916738439135459317 := by
  unfold tailWord_6505044
  simp only [CollatzResearch.WordTrace]
  refine ⟨118629223122672017955613093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158172297496896023940817457 118629223122672017955613093)
  ·
    refine ⟨22242979335501003366677455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118629223122672017955613093 22242979335501003366677455)
    ·
      refine ⟨33364469003251505050016183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242979335501003366677455 33364469003251505050016183)
      ·
        refine ⟨50046703504877257575024275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33364469003251505050016183 50046703504877257575024275)
        ·
          refine ⟨75070055257315886362536413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50046703504877257575024275 75070055257315886362536413)
          ·
            refine ⟨28151270721493457385951155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75070055257315886362536413 28151270721493457385951155)
            ·
              refine ⟨42226906082240186078926733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28151270721493457385951155 42226906082240186078926733)
              ·
                refine ⟨15835089780840069779597525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42226906082240186078926733 15835089780840069779597525)
                ·
                  refine ⟨371134916738439135459317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15835089780840069779597525 371134916738439135459317)
                  ·
                    rfl

theorem cell23_6505044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6505044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505044 prefixEnd_6505044 := by exact prefixLift 6505044
  have htrace : WordTrace (prefixWord ++ tailWord_6505044) baseStart_6505044 baseEnd_6505044 := by
    simpa [prefixWord, tailWord_6505044, baseEnd_6505044] using wordTrace_append hprefix tailTrace_6505044
  have hstable : (prefixWord ++ tailWord_6505044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505044).length < 2 ^ (prefixWord ++ tailWord_6505044).sum := by decide
  have hdescent : baseEnd_6505044 < baseStart_6505044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505067 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_6505067 : Nat := 118140960795 + 6505067 * 2 ^ 59
def prefixEnd_6505067 : Nat := 4983230072969 + 3 ^ 40 * 6505067 * 2
def baseEnd_6505067 : Nat := 3340226060701005629146247

theorem tailTrace_6505067 : CollatzResearch.WordTrace tailWord_6505067 prefixEnd_6505067 3340226060701005629146247 := by
  unfold tailWord_6505067
  simp only [CollatzResearch.WordTrace]
  refine ⟨237259285124260710839313455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158172856749507140559542303 237259285124260710839313455)
  ·
    refine ⟨355888927686391066258970183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237259285124260710839313455 355888927686391066258970183)
    ·
      refine ⟨533833391529586599388455275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355888927686391066258970183 533833391529586599388455275)
      ·
        refine ⟨800750087294379899082682913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533833391529586599388455275 800750087294379899082682913)
        ·
          refine ⟨600562565470784924312012185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800750087294379899082682913 600562565470784924312012185)
          ·
            refine ⟨450421924103088693234009139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600562565470784924312012185 450421924103088693234009139)
            ·
              refine ⟨675632886154633039851013709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450421924103088693234009139 675632886154633039851013709)
              ·
                refine ⟨253362332307987389944130141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675632886154633039851013709 253362332307987389944130141)
                ·
                  refine ⟨95010874615495271229048803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253362332307987389944130141 95010874615495271229048803)
                  ·
                    refine ⟨142516311923242906843573205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95010874615495271229048803 142516311923242906843573205)
                    ·
                      refine ⟨3340226060701005629146247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142516311923242906843573205 3340226060701005629146247)
                      ·
                        rfl

theorem cell23_6505067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_6505067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505067 prefixEnd_6505067 := by exact prefixLift 6505067
  have htrace : WordTrace (prefixWord ++ tailWord_6505067) baseStart_6505067 baseEnd_6505067 := by
    simpa [prefixWord, tailWord_6505067, baseEnd_6505067] using wordTrace_append hprefix tailTrace_6505067
  have hstable : (prefixWord ++ tailWord_6505067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505067).length < 2 ^ (prefixWord ++ tailWord_6505067).sum := by decide
  have hdescent : baseEnd_6505067 < baseStart_6505067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505111 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_6505111 : Nat := 118140960795 + 6505111 * 2 ^ 59
def prefixEnd_6505111 : Nat := 4983230072969 + 3 ^ 40 * 6505111 * 2
def baseEnd_6505111 : Nat := 3340248653849803456996045

theorem tailTrace_6505111 : CollatzResearch.WordTrace tailWord_6505111 prefixEnd_6505111 3340248653849803456996045 := by
  unfold tailWord_6505111
  simp only [CollatzResearch.WordTrace]
  refine ⟨237260889936101306353915187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158173926624067537569276791 237260889936101306353915187)
  ·
    refine ⟨355891334904151959530872781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237260889936101306353915187 355891334904151959530872781)
    ·
      refine ⟨133459250589056984824077293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355891334904151959530872781 133459250589056984824077293)
      ·
        refine ⟨50047218970896369309028985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133459250589056984824077293 50047218970896369309028985)
        ·
          refine ⟨37535414228172276981771739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50047218970896369309028985 37535414228172276981771739)
          ·
            refine ⟨56303121342258415472657609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37535414228172276981771739 56303121342258415472657609)
            ·
              refine ⟨42227341006693811604493207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56303121342258415472657609 42227341006693811604493207)
              ·
                refine ⟨63341011510040717406739811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42227341006693811604493207 63341011510040717406739811)
                ·
                  refine ⟨95011517265061076110109717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63341011510040717406739811 95011517265061076110109717)
                  ·
                    refine ⟨4453664871799737942661393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95011517265061076110109717 4453664871799737942661393)
                    ·
                      refine ⟨3340248653849803456996045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453664871799737942661393 3340248653849803456996045)
                      ·
                        rfl

theorem cell23_6505111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_6505111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505111 prefixEnd_6505111 := by exact prefixLift 6505111
  have htrace : WordTrace (prefixWord ++ tailWord_6505111) baseStart_6505111 baseEnd_6505111 := by
    simpa [prefixWord, tailWord_6505111, baseEnd_6505111] using wordTrace_append hprefix tailTrace_6505111
  have hstable : (prefixWord ++ tailWord_6505111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505111).length < 2 ^ (prefixWord ++ tailWord_6505111).sum := by decide
  have hdescent : baseEnd_6505111 < baseStart_6505111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505138 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_6505138 : Nat := 118140960795 + 6505138 * 2 ^ 59
def prefixEnd_6505138 : Nat := 4983230072969 + 3 ^ 40 * 6505138 * 2
def baseEnd_6505138 : Nat := 1113420839275824950452807

theorem tailTrace_6505138 : CollatzResearch.WordTrace tailWord_6505138 prefixEnd_6505138 1113420839275824950452807 := by
  unfold tailWord_6505138
  simp only [CollatzResearch.WordTrace]
  refine ⟨59315468676750872491287017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158174583138002326643432045 59315468676750872491287017)
  ·
    refine ⟨44486601507563154368465263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59315468676750872491287017 44486601507563154368465263)
    ·
      refine ⟨66729902261344731552697895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44486601507563154368465263 66729902261344731552697895)
      ·
        refine ⟨100094853392017097329046843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66729902261344731552697895 100094853392017097329046843)
        ·
          refine ⟨150142280088025645993570265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100094853392017097329046843 150142280088025645993570265)
          ·
            refine ⟨112606710066019234495177699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150142280088025645993570265 112606710066019234495177699)
            ·
              refine ⟨168910065099028851742766549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112606710066019234495177699 168910065099028851742766549)
              ·
                refine ⟨3958829650758488712721091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168910065099028851742766549 3958829650758488712721091)
                ·
                  refine ⟨5938244476137733069081637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958829650758488712721091 5938244476137733069081637)
                  ·
                    refine ⟨1113420839275824950452807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938244476137733069081637 1113420839275824950452807)
                    ·
                      rfl

theorem cell23_6505138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_6505138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505138 prefixEnd_6505138 := by exact prefixLift 6505138
  have htrace : WordTrace (prefixWord ++ tailWord_6505138) baseStart_6505138 baseEnd_6505138 := by
    simpa [prefixWord, tailWord_6505138, baseEnd_6505138] using wordTrace_append hprefix tailTrace_6505138
  have hstable : (prefixWord ++ tailWord_6505138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505138).length < 2 ^ (prefixWord ++ tailWord_6505138).sum := by decide
  have hdescent : baseEnd_6505138 < baseStart_6505138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505151 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 6]
def baseStart_6505151 : Nat := 118140960795 + 6505151 * 2 ^ 59
def prefixEnd_6505151 : Nat := 4983230072969 + 3 ^ 40 * 6505151 * 2
def baseEnd_6505151 : Nat := 371141021452887033388429

theorem tailTrace_6505151 : CollatzResearch.WordTrace tailWord_6505151 prefixEnd_6505151 371141021452887033388429 := by
  unfold tailWord_6505151
  simp only [CollatzResearch.WordTrace]
  refine ⟨237262348855956393185371307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158174899237304262123580871 237262348855956393185371307)
  ·
    refine ⟨355893523283934589778056961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237262348855956393185371307 355893523283934589778056961)
    ·
      refine ⟨266920142462950942333542721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355893523283934589778056961 266920142462950942333542721)
      ·
        refine ⟨200190106847213206750157041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266920142462950942333542721 200190106847213206750157041)
        ·
          refine ⟨150142580135409905062617781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200190106847213206750157041 150142580135409905062617781)
          ·
            refine ⟨14075866887694678599620417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150142580135409905062617781 14075866887694678599620417)
            ·
              refine ⟨10556900165771008949715313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14075866887694678599620417 10556900165771008949715313)
              ·
                refine ⟨7917675124328256712286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10556900165771008949715313 7917675124328256712286485)
                ·
                  refine ⟨371141021452887033388429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7917675124328256712286485 371141021452887033388429)
                  ·
                    rfl

theorem cell23_6505151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 6].length) (baseStart_6505151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505151 prefixEnd_6505151 := by exact prefixLift 6505151
  have htrace : WordTrace (prefixWord ++ tailWord_6505151) baseStart_6505151 baseEnd_6505151 := by
    simpa [prefixWord, tailWord_6505151, baseEnd_6505151] using wordTrace_append hprefix tailTrace_6505151
  have hstable : (prefixWord ++ tailWord_6505151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505151).length < 2 ^ (prefixWord ++ tailWord_6505151).sum := by decide
  have hdescent : baseEnd_6505151 < baseStart_6505151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505161 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 3]
def baseStart_6505161 : Nat := 118140960795 + 6505161 * 2 ^ 59
def prefixEnd_6505161 : Nat := 4983230072969 + 3 ^ 40 * 6505161 * 2
def baseEnd_6505161 : Nat := 3340274327882528261370815

theorem tailTrace_6505161 : CollatzResearch.WordTrace tailWord_6505161 prefixEnd_6505161 3340274327882528261370815 := by
  unfold tailWord_6505161
  simp only [CollatzResearch.WordTrace]
  refine ⟨237262713585920164893235337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158175142390613443262156891 237262713585920164893235337)
  ·
    refine ⟨177947035189440123669926503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237262713585920164893235337 177947035189440123669926503)
    ·
      refine ⟨266920552784160185504889755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177947035189440123669926503 266920552784160185504889755)
      ·
        refine ⟨400380829176240278257334633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266920552784160185504889755 400380829176240278257334633)
        ·
          refine ⟨300285621882180208693000975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400380829176240278257334633 300285621882180208693000975)
          ·
            refine ⟨450428432823270313039501463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300285621882180208693000975 450428432823270313039501463)
            ·
              refine ⟨675642649234905469559252195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450428432823270313039501463 675642649234905469559252195)
              ·
                refine ⟨1013463973852358204338878293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675642649234905469559252195 1013463973852358204338878293)
                ·
                  refine ⟨5938265471791161353548115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1013463973852358204338878293 5938265471791161353548115)
                  ·
                    refine ⟨8907398207686742030322173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5938265471791161353548115 8907398207686742030322173)
                    ·
                      refine ⟨3340274327882528261370815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907398207686742030322173 3340274327882528261370815)
                      ·
                        rfl

theorem cell23_6505161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_6505161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505161 prefixEnd_6505161 := by exact prefixLift 6505161
  have htrace : WordTrace (prefixWord ++ tailWord_6505161) baseStart_6505161 baseEnd_6505161 := by
    simpa [prefixWord, tailWord_6505161, baseEnd_6505161] using wordTrace_append hprefix tailTrace_6505161
  have hstable : (prefixWord ++ tailWord_6505161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505161).length < 2 ^ (prefixWord ++ tailWord_6505161).sum := by decide
  have hdescent : baseEnd_6505161 < baseStart_6505161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505178 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_6505178 : Nat := 118140960795 + 6505178 * 2 ^ 59
def prefixEnd_6505178 : Nat := 4983230072969 + 3 ^ 40 * 6505178 * 2
def baseEnd_6505178 : Nat := 3340283057053654694858237

theorem tailTrace_6505178 : CollatzResearch.WordTrace tailWord_6505178 prefixEnd_6505178 3340283057053654694858237 := by
  unfold tailWord_6505178
  simp only [CollatzResearch.WordTrace]
  refine ⟨59315833406714644199151047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158175555751239051197736125 59315833406714644199151047)
  ·
    refine ⟨88973750110071966298726571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59315833406714644199151047 88973750110071966298726571)
    ·
      refine ⟨133460625165107949448089857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88973750110071966298726571 133460625165107949448089857)
      ·
        refine ⟨100095468873830962086067393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133460625165107949448089857 100095468873830962086067393)
        ·
          refine ⟨75071601655373221564550545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100095468873830962086067393 75071601655373221564550545)
          ·
            refine ⟨56303701241529916173412909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75071601655373221564550545 56303701241529916173412909)
            ·
              refine ⟨21113887965573718565029841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56303701241529916173412909 21113887965573718565029841)
              ·
                refine ⟨15835415974180288923772381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21113887965573718565029841 15835415974180288923772381)
                ·
                  refine ⟨5938280990317608346414643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15835415974180288923772381 5938280990317608346414643)
                  ·
                    refine ⟨8907421485476412519621965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5938280990317608346414643 8907421485476412519621965)
                    ·
                      refine ⟨3340283057053654694858237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907421485476412519621965 3340283057053654694858237)
                      ·
                        rfl

theorem cell23_6505178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_6505178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505178 prefixEnd_6505178 := by exact prefixLift 6505178
  have htrace : WordTrace (prefixWord ++ tailWord_6505178) baseStart_6505178 baseEnd_6505178 := by
    simpa [prefixWord, tailWord_6505178, baseEnd_6505178] using wordTrace_append hprefix tailTrace_6505178
  have hstable : (prefixWord ++ tailWord_6505178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505178).length < 2 ^ (prefixWord ++ tailWord_6505178).sum := by decide
  have hdescent : baseEnd_6505178 < baseStart_6505178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505188 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_6505188 : Nat := 118140960795 + 6505188 * 2 ^ 59
def prefixEnd_6505188 : Nat := 4983230072969 + 3 ^ 40 * 6505188 * 2
def baseEnd_6505188 : Nat := 3340288191860199655733191

theorem tailTrace_6505188 : CollatzResearch.WordTrace tailWord_6505188 prefixEnd_6505188 3340288191860199655733191 := by
  unfold tailWord_6505188
  simp only [CollatzResearch.WordTrace]
  refine ⟨118631849178411174252234109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158175798904548232336312145 118631849178411174252234109)
  ·
    refine ⟨44486943441904190344587791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118631849178411174252234109 44486943441904190344587791)
    ·
      refine ⟨66730415162856285516881687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44486943441904190344587791 66730415162856285516881687)
      ·
        refine ⟨100095622744284428275322531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66730415162856285516881687 100095622744284428275322531)
        ·
          refine ⟨150143434116426642412983797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100095622744284428275322531 150143434116426642412983797)
          ·
            refine ⟨14075946948414997726217231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150143434116426642412983797 14075946948414997726217231)
            ·
              refine ⟨21113920422622496589325847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14075946948414997726217231 21113920422622496589325847)
              ·
                refine ⟨31670880633933744883988771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21113920422622496589325847 31670880633933744883988771)
                ·
                  refine ⟨47506320950900617325983157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31670880633933744883988771 47506320950900617325983157)
                  ·
                    refine ⟨4453717589146932874310921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47506320950900617325983157 4453717589146932874310921)
                    ·
                      refine ⟨3340288191860199655733191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453717589146932874310921 3340288191860199655733191)
                      ·
                        rfl

theorem cell23_6505188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_6505188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505188 prefixEnd_6505188 := by exact prefixLift 6505188
  have htrace : WordTrace (prefixWord ++ tailWord_6505188) baseStart_6505188 baseEnd_6505188 := by
    simpa [prefixWord, tailWord_6505188, baseEnd_6505188] using wordTrace_append hprefix tailTrace_6505188
  have hstable : (prefixWord ++ tailWord_6505188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505188).length < 2 ^ (prefixWord ++ tailWord_6505188).sum := by decide
  have hdescent : baseEnd_6505188 < baseStart_6505188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505198 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6505198 : Nat := 118140960795 + 6505198 * 2 ^ 59
def prefixEnd_6505198 : Nat := 4983230072969 + 3 ^ 40 * 6505198 * 2
def baseEnd_6505198 : Nat := 1113431108888914872202715

theorem tailTrace_6505198 : CollatzResearch.WordTrace tailWord_6505198 prefixEnd_6505198 1113431108888914872202715 := by
  unfold tailWord_6505198
  simp only [CollatzResearch.WordTrace]
  refine ⟨29658007885848265026541531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158176042057857413474888165 29658007885848265026541531)
  ·
    refine ⟨44487011828772397539812297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29658007885848265026541531 44487011828772397539812297)
    ·
      refine ⟨33365258871579298154859223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44487011828772397539812297 33365258871579298154859223)
      ·
        refine ⟨50047888307368947232288835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33365258871579298154859223 50047888307368947232288835)
        ·
          refine ⟨75071832461053420848433253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50047888307368947232288835 75071832461053420848433253)
          ·
            refine ⟨14075968586447516409081235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75071832461053420848433253 14075968586447516409081235)
            ·
              refine ⟨21113952879671274613621853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14075968586447516409081235 21113952879671274613621853)
              ·
                refine ⟨7917732329876727980108195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21113952879671274613621853 7917732329876727980108195)
                ·
                  refine ⟨11876598494815091970162293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917732329876727980108195 11876598494815091970162293)
                  ·
                    refine ⟨1113431108888914872202715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11876598494815091970162293 1113431108888914872202715)
                    ·
                      rfl

theorem cell23_6505198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6505198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505198 prefixEnd_6505198 := by exact prefixLift 6505198
  have htrace : WordTrace (prefixWord ++ tailWord_6505198) baseStart_6505198 baseEnd_6505198 := by
    simpa [prefixWord, tailWord_6505198, baseEnd_6505198] using wordTrace_append hprefix tailTrace_6505198
  have hstable : (prefixWord ++ tailWord_6505198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505198).length < 2 ^ (prefixWord ++ tailWord_6505198).sum := by decide
  have hdescent : baseEnd_6505198 < baseStart_6505198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505221 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_6505221 : Nat := 118140960795 + 6505221 * 2 ^ 59
def prefixEnd_6505221 : Nat := 4983230072969 + 3 ^ 40 * 6505221 * 2
def baseEnd_6505221 : Nat := 3340305136721798026620539

theorem tailTrace_6505221 : CollatzResearch.WordTrace tailWord_6505221 prefixEnd_6505221 3340305136721798026620539 := by
  unfold tailWord_6505221
  simp only [CollatzResearch.WordTrace]
  refine ⟨237264901965702795140419517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158176601310468530093613011 237264901965702795140419517)
  ·
    refine ⟨88974338237138548177657319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237264901965702795140419517 88974338237138548177657319)
    ·
      refine ⟨133461507355707822266485979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88974338237138548177657319 133461507355707822266485979)
      ·
        refine ⟨200192261033561733399728969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133461507355707822266485979 200192261033561733399728969)
        ·
          refine ⟨150144195775171300049796727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200192261033561733399728969 150144195775171300049796727)
          ·
            refine ⟨225216293662756950074695091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150144195775171300049796727 225216293662756950074695091)
            ·
              refine ⟨337824440494135425112042637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225216293662756950074695091 337824440494135425112042637)
              ·
                refine ⟨126684165185300784417015989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337824440494135425112042637 126684165185300784417015989)
                ·
                  refine ⟨11876640486121948539095249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126684165185300784417015989 11876640486121948539095249)
                  ·
                    refine ⟨8907480364591461404321437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11876640486121948539095249 8907480364591461404321437)
                    ·
                      refine ⟨3340305136721798026620539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907480364591461404321437 3340305136721798026620539)
                      ·
                        rfl

theorem cell23_6505221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_6505221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505221 prefixEnd_6505221 := by exact prefixLift 6505221
  have htrace : WordTrace (prefixWord ++ tailWord_6505221) baseStart_6505221 baseEnd_6505221 := by
    simpa [prefixWord, tailWord_6505221, baseEnd_6505221] using wordTrace_append hprefix tailTrace_6505221
  have hstable : (prefixWord ++ tailWord_6505221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505221).length < 2 ^ (prefixWord ++ tailWord_6505221).sum := by decide
  have hdescent : baseEnd_6505221 < baseStart_6505221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505251 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3]
def baseStart_6505251 : Nat := 118140960795 + 6505251 * 2 ^ 59
def prefixEnd_6505251 : Nat := 4983230072969 + 3 ^ 40 * 6505251 * 2
def baseEnd_6505251 : Nat := 3340320541141432909245401

theorem tailTrace_6505251 : CollatzResearch.WordTrace tailWord_6505251 prefixEnd_6505251 3340320541141432909245401 := by
  unfold tailWord_6505251
  simp only [CollatzResearch.WordTrace]
  refine ⟨237265996155594110264011607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158177330770396073509341071 237265996155594110264011607)
  ·
    refine ⟨355898994233391165396017411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237265996155594110264011607 355898994233391165396017411)
    ·
      refine ⟨533848491350086748094026117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355898994233391165396017411 533848491350086748094026117)
      ·
        refine ⟨100096592128141265267629897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 533848491350086748094026117 100096592128141265267629897)
        ·
          refine ⟨75072444096105948950722423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100096592128141265267629897 75072444096105948950722423)
          ·
            refine ⟨112608666144158923426083635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75072444096105948950722423 112608666144158923426083635)
            ·
              refine ⟨168912999216238385139125453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112608666144158923426083635 168912999216238385139125453)
              ·
                refine ⟨63342374706089394427172045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168912999216238385139125453 63342374706089394427172045)
                ·
                  refine ⟨23753390514783522910189517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63342374706089394427172045 23753390514783522910189517)
                  ·
                    refine ⟨8907521443043821091321069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23753390514783522910189517 8907521443043821091321069)
                    ·
                      refine ⟨3340320541141432909245401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907521443043821091321069 3340320541141432909245401)
                      ·
                        rfl

theorem cell23_6505251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_6505251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505251 prefixEnd_6505251 := by exact prefixLift 6505251
  have htrace : WordTrace (prefixWord ++ tailWord_6505251) baseStart_6505251 baseEnd_6505251 := by
    simpa [prefixWord, tailWord_6505251, baseEnd_6505251] using wordTrace_append hprefix tailTrace_6505251
  have hstable : (prefixWord ++ tailWord_6505251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505251).length < 2 ^ (prefixWord ++ tailWord_6505251).sum := by decide
  have hdescent : baseEnd_6505251 < baseStart_6505251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505286 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6505286 : Nat := 118140960795 + 6505286 * 2 ^ 59
def prefixEnd_6505286 : Nat := 4983230072969 + 3 ^ 40 * 6505286 * 2
def baseEnd_6505286 : Nat := 3340338512964340272307741

theorem tailTrace_6505286 : CollatzResearch.WordTrace tailWord_6505286 prefixEnd_6505286 3340338512964340272307741 := by
  unfold tailWord_6505286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414602272202103476297991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158178181806978207494357141 7414602272202103476297991)
  ·
    refine ⟨11121903408303155214446987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7414602272202103476297991 11121903408303155214446987)
    ·
      refine ⟨16682855112454732821670481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11121903408303155214446987 16682855112454732821670481)
      ·
        refine ⟨12512141334341049616252861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16682855112454732821670481 12512141334341049616252861)
        ·
          refine ⟨4692053000377893606094823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12512141334341049616252861 4692053000377893606094823)
          ·
            refine ⟨7038079500566840409142235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692053000377893606094823 7038079500566840409142235)
            ·
              refine ⟨10557119250850260613713353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038079500566840409142235 10557119250850260613713353)
              ·
                refine ⟨7917839438137695460285015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10557119250850260613713353 7917839438137695460285015)
                ·
                  refine ⟨11876759157206543190427523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917839438137695460285015 11876759157206543190427523)
                  ·
                    refine ⟨17815138735809814785641285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11876759157206543190427523 17815138735809814785641285)
                    ·
                      refine ⟨3340338512964340272307741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17815138735809814785641285 3340338512964340272307741)
                      ·
                        rfl

theorem cell23_6505286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6505286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505286 prefixEnd_6505286 := by exact prefixLift 6505286
  have htrace : WordTrace (prefixWord ++ tailWord_6505286) baseStart_6505286 baseEnd_6505286 := by
    simpa [prefixWord, tailWord_6505286, baseEnd_6505286] using wordTrace_append hprefix tailTrace_6505286
  have hstable : (prefixWord ++ tailWord_6505286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505286).length < 2 ^ (prefixWord ++ tailWord_6505286).sum := by decide
  have hdescent : baseEnd_6505286 < baseStart_6505286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505311 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_6505311 : Nat := 118140960795 + 6505311 * 2 ^ 59
def prefixEnd_6505311 : Nat := 4983230072969 + 3 ^ 40 * 6505311 * 2
def baseEnd_6505311 : Nat := 3340351349980702674495125

theorem tailTrace_6505311 : CollatzResearch.WordTrace tailWord_6505311 prefixEnd_6505311 3340351349980702674495125 := by
  unfold tailWord_6505311
  simp only [CollatzResearch.WordTrace]
  refine ⟨237268184535376740511195787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158178789690251160340797191 237268184535376740511195787)
  ·
    refine ⟨355902276803065110766793681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237268184535376740511195787 355902276803065110766793681)
    ·
      refine ⟨266926707602298833075095261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355902276803065110766793681 266926707602298833075095261)
      ·
        refine ⟨100097515350862062403160723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266926707602298833075095261 100097515350862062403160723)
        ·
          refine ⟨150146273026293093604741085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100097515350862062403160723 150146273026293093604741085)
          ·
            refine ⟨56304852384859910101777907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150146273026293093604741085 56304852384859910101777907)
            ·
              refine ⟨84457278577289865152666861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56304852384859910101777907 84457278577289865152666861)
              ·
                refine ⟨31671479466483699432250073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84457278577289865152666861 31671479466483699432250073)
                ·
                  refine ⟨23753609599862774574187555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31671479466483699432250073 23753609599862774574187555)
                  ·
                    refine ⟨35630414399794161861281333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23753609599862774574187555 35630414399794161861281333)
                    ·
                      refine ⟨3340351349980702674495125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35630414399794161861281333 3340351349980702674495125)
                      ·
                        rfl

theorem cell23_6505311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_6505311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505311 prefixEnd_6505311 := by exact prefixLift 6505311
  have htrace : WordTrace (prefixWord ++ tailWord_6505311) baseStart_6505311 baseEnd_6505311 := by
    simpa [prefixWord, tailWord_6505311, baseEnd_6505311] using wordTrace_append hprefix tailTrace_6505311
  have hstable : (prefixWord ++ tailWord_6505311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505311).length < 2 ^ (prefixWord ++ tailWord_6505311).sum := by decide
  have hdescent : baseEnd_6505311 < baseStart_6505311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505312 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2]
def baseStart_6505312 : Nat := 118140960795 + 6505312 * 2 ^ 59
def prefixEnd_6505312 : Nat := 4983230072969 + 3 ^ 40 * 6505312 * 2
def baseEnd_6505312 : Nat := 3340351863461357170582621

theorem tailTrace_6505312 : CollatzResearch.WordTrace tailWord_6505312 prefixEnd_6505312 3340351863461357170582621 := by
  unfold tailWord_6505312
  simp only [CollatzResearch.WordTrace]
  refine ⟨118634110504186558840991095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158178814005582078454654793 118634110504186558840991095)
  ·
    refine ⟨177951165756279838261486643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118634110504186558840991095 177951165756279838261486643)
    ·
      refine ⟨266926748634419757392229965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177951165756279838261486643 266926748634419757392229965)
      ·
        refine ⟨100097530737907409022086237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266926748634419757392229965 100097530737907409022086237)
        ·
          refine ⟨37536574026715278383282339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100097530737907409022086237 37536574026715278383282339)
          ·
            refine ⟨56304861040072917574923509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37536574026715278383282339 56304861040072917574923509)
            ·
              refine ⟨5278580722506836022649079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56304861040072917574923509 5278580722506836022649079)
              ·
                refine ⟨7917871083760254033973619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278580722506836022649079 7917871083760254033973619)
                ·
                  refine ⟨11876806625640381050960429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7917871083760254033973619 11876806625640381050960429)
                  ·
                    refine ⟨4453802484615142894110161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11876806625640381050960429 4453802484615142894110161)
                    ·
                      refine ⟨3340351863461357170582621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453802484615142894110161 3340351863461357170582621)
                      ·
                        rfl

theorem cell23_6505312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_6505312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505312 prefixEnd_6505312 := by exact prefixLift 6505312
  have htrace : WordTrace (prefixWord ++ tailWord_6505312) baseStart_6505312 baseEnd_6505312 := by
    simpa [prefixWord, tailWord_6505312, baseEnd_6505312] using wordTrace_append hprefix tailTrace_6505312
  have hstable : (prefixWord ++ tailWord_6505312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505312).length < 2 ^ (prefixWord ++ tailWord_6505312).sum := by decide
  have hdescent : baseEnd_6505312 < baseStart_6505312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505365 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 5]
def baseStart_6505365 : Nat := 118140960795 + 6505365 * 2 ^ 59
def prefixEnd_6505365 : Nat := 4983230072969 + 3 ^ 40 * 6505365 * 2
def baseEnd_6505365 : Nat := 371153230881782829246653

theorem tailTrace_6505365 : CollatzResearch.WordTrace tailWord_6505365 prefixEnd_6505365 371153230881782829246653 := by
  unfold tailWord_6505365
  simp only [CollatzResearch.WordTrace]
  refine ⟨237270154077181107733661549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158180102718120738489107699 237270154077181107733661549)
  ·
    refine ⟨88976307778942915400123081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237270154077181107733661549 88976307778942915400123081)
    ·
      refine ⟨66732230834207186550092311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88976307778942915400123081 66732230834207186550092311)
      ·
        refine ⟨100098346251310779825138467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66732230834207186550092311 100098346251310779825138467)
        ·
          refine ⟨150147519376966169737707701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100098346251310779825138467 150147519376966169737707701)
          ·
            refine ⟨14076329941590578412910097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150147519376966169737707701 14076329941590578412910097)
            ·
              refine ⟨10557247456192933809682573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14076329941590578412910097 10557247456192933809682573)
              ·
                refine ⟨3958967796072350178630965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10557247456192933809682573 3958967796072350178630965)
                ·
                  refine ⟨371153230881782829246653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3958967796072350178630965 371153230881782829246653)
                  ·
                    rfl

theorem cell23_6505365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_6505365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505365 prefixEnd_6505365 := by exact prefixLift 6505365
  have htrace : WordTrace (prefixWord ++ tailWord_6505365) baseStart_6505365 baseEnd_6505365 := by
    simpa [prefixWord, tailWord_6505365, baseEnd_6505365] using wordTrace_append hprefix tailTrace_6505365
  have hstable : (prefixWord ++ tailWord_6505365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505365).length < 2 ^ (prefixWord ++ tailWord_6505365).sum := by decide
  have hdescent : baseEnd_6505365 < baseStart_6505365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505411 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_6505411 : Nat := 118140960795 + 6505411 * 2 ^ 59
def prefixEnd_6505411 : Nat := 4983230072969 + 3 ^ 40 * 6505411 * 2
def baseEnd_6505411 : Nat := 3340402698046152283244665

theorem tailTrace_6505411 : CollatzResearch.WordTrace tailWord_6505411 prefixEnd_6505411 3340402698046152283244665 := by
  unfold tailWord_6505411
  simp only [CollatzResearch.WordTrace]
  refine ⟨237271831835014457589836087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158181221223342971726557391 237271831835014457589836087)
  ·
    refine ⟨355907747752521686384754131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237271831835014457589836087 355907747752521686384754131)
    ·
      refine ⟨533861621628782529577131197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355907747752521686384754131 533861621628782529577131197)
      ·
        refine ⟨200198108110793448591424199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533861621628782529577131197 200198108110793448591424199)
        ·
          refine ⟨300297162166190172887136299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200198108110793448591424199 300297162166190172887136299)
          ·
            refine ⟨450445743249285259330704449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300297162166190172887136299 450445743249285259330704449)
            ·
              refine ⟨337834307436963944498028337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450445743249285259330704449 337834307436963944498028337)
              ·
                refine ⟨253375730577722958373521253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337834307436963944498028337 253375730577722958373521253)
                ·
                  refine ⟨47507949483323054695035235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253375730577722958373521253 47507949483323054695035235)
                  ·
                    refine ⟨71261924224984582042552853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47507949483323054695035235 71261924224984582042552853)
                    ·
                      refine ⟨3340402698046152283244665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71261924224984582042552853 3340402698046152283244665)
                      ·
                        rfl

theorem cell23_6505411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_6505411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505411 prefixEnd_6505411 := by exact prefixLift 6505411
  have htrace : WordTrace (prefixWord ++ tailWord_6505411) baseStart_6505411 baseEnd_6505411 := by
    simpa [prefixWord, tailWord_6505411, baseEnd_6505411] using wordTrace_append hprefix tailTrace_6505411
  have hstable : (prefixWord ++ tailWord_6505411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505411).length < 2 ^ (prefixWord ++ tailWord_6505411).sum := by decide
  have hdescent : baseEnd_6505411 < baseStart_6505411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505451 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 11]
def baseStart_6505451 : Nat := 118140960795 + 6505451 * 2 ^ 59
def prefixEnd_6505451 : Nat := 4983230072969 + 3 ^ 40 * 6505451 * 2
def baseEnd_6505451 : Nat := 1113474412424110708914827

theorem tailTrace_6505451 : CollatzResearch.WordTrace tailWord_6505451 prefixEnd_6505451 1113474412424110708914827 := by
  unfold tailWord_6505451
  simp only [CollatzResearch.WordTrace]
  refine ⟨237273290754869544421292207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158182193836579696280861471 237273290754869544421292207)
  ·
    refine ⟨355909936132304316631938311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237273290754869544421292207 355909936132304316631938311)
    ·
      refine ⟨533864904198456474947907467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355909936132304316631938311 533864904198456474947907467)
      ·
        refine ⟨800797356297684712421861201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533864904198456474947907467 800797356297684712421861201)
        ·
          refine ⟨600598017223263534316395901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800797356297684712421861201 600598017223263534316395901)
          ·
            refine ⟨225224256458723825368648463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600598017223263534316395901 225224256458723825368648463)
            ·
              refine ⟨337836384688085738052972695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225224256458723825368648463 337836384688085738052972695)
              ·
                refine ⟨506754577032128607079459043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337836384688085738052972695 506754577032128607079459043)
                ·
                  refine ⟨760131865548192910619188565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506754577032128607079459043 760131865548192910619188565)
                  ·
                    refine ⟨1113474412424110708914827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 760131865548192910619188565 1113474412424110708914827)
                    ·
                      rfl

theorem cell23_6505451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_6505451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505451 prefixEnd_6505451 := by exact prefixLift 6505451
  have htrace : WordTrace (prefixWord ++ tailWord_6505451) baseStart_6505451 baseEnd_6505451 := by
    simpa [prefixWord, tailWord_6505451, baseEnd_6505451] using wordTrace_append hprefix tailTrace_6505451
  have hstable : (prefixWord ++ tailWord_6505451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505451).length < 2 ^ (prefixWord ++ tailWord_6505451).sum := by decide
  have hdescent : baseEnd_6505451 < baseStart_6505451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505455 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 6]
def baseStart_6505455 : Nat := 118140960795 + 6505455 * 2 ^ 59
def prefixEnd_6505455 : Nat := 4983230072969 + 3 ^ 40 * 6505455 * 2
def baseEnd_6505455 : Nat := 371158365688327790121607

theorem tailTrace_6505455 : CollatzResearch.WordTrace tailWord_6505455 prefixEnd_6505455 371158365688327790121607 := by
  unfold tailWord_6505455
  simp only [CollatzResearch.WordTrace]
  refine ⟨237273436646855053104437819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158182291097903368736291879 237273436646855053104437819)
  ·
    refine ⟨355910154970282579656656729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237273436646855053104437819 355910154970282579656656729)
    ·
      refine ⟨266932616227711934742492547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355910154970282579656656729 266932616227711934742492547)
      ·
        refine ⟨400398924341567902113738821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266932616227711934742492547 400398924341567902113738821)
        ·
          refine ⟨75074798314043981646326029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400398924341567902113738821 75074798314043981646326029)
          ·
            refine ⟨28153049367766493117372261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75074798314043981646326029 28153049367766493117372261)
            ·
              refine ⟨5278696756456217459507299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28153049367766493117372261 5278696756456217459507299)
              ·
                refine ⟨7918045134684326189260949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5278696756456217459507299 7918045134684326189260949)
                ·
                  refine ⟨371158365688327790121607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7918045134684326189260949 371158365688327790121607)
                  ·
                    rfl

theorem cell23_6505455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 6].length) (baseStart_6505455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505455 prefixEnd_6505455 := by exact prefixLift 6505455
  have htrace : WordTrace (prefixWord ++ tailWord_6505455) baseStart_6505455 baseEnd_6505455 := by
    simpa [prefixWord, tailWord_6505455, baseEnd_6505455] using wordTrace_append hprefix tailTrace_6505455
  have hstable : (prefixWord ++ tailWord_6505455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505455).length < 2 ^ (prefixWord ++ tailWord_6505455).sum := by decide
  have hdescent : baseEnd_6505455 < baseStart_6505455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505465 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 3]
def baseStart_6505465 : Nat := 118140960795 + 6505465 * 2 ^ 59
def prefixEnd_6505465 : Nat := 4983230072969 + 3 ^ 40 * 6505465 * 2
def baseEnd_6505465 : Nat := 3340430426001495071969417

theorem tailTrace_6505465 : CollatzResearch.WordTrace tailWord_6505465 prefixEnd_6505465 3340430426001495071969417 := by
  unfold tailWord_6505465
  simp only [CollatzResearch.WordTrace]
  refine ⟨237273801376818824812301849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158182534251212549874867899 237273801376818824812301849)
  ·
    refine ⟨177955351032614118609226387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237273801376818824812301849 177955351032614118609226387)
    ·
      refine ⟨266933026548921177913839581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177955351032614118609226387 266933026548921177913839581)
      ·
        refine ⟨100099884955845441717689843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266933026548921177913839581 100099884955845441717689843)
        ·
          refine ⟨150149827433768162576534765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100099884955845441717689843 150149827433768162576534765)
          ·
            refine ⟨56306185287663060966200537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150149827433768162576534765 56306185287663060966200537)
            ·
              refine ⟨42229638965747295724650403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56306185287663060966200537 42229638965747295724650403)
              ·
                refine ⟨63344458448620943586975605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42229638965747295724650403 63344458448620943586975605)
                ·
                  refine ⟨5938542979558213461278963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63344458448620943586975605 5938542979558213461278963)
                  ·
                    refine ⟨8907814469337320191918445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5938542979558213461278963 8907814469337320191918445)
                    ·
                      refine ⟨3340430426001495071969417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907814469337320191918445 3340430426001495071969417)
                      ·
                        rfl

theorem cell23_6505465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_6505465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505465 prefixEnd_6505465 := by exact prefixLift 6505465
  have htrace : WordTrace (prefixWord ++ tailWord_6505465) baseStart_6505465 baseEnd_6505465 := by
    simpa [prefixWord, tailWord_6505465, baseEnd_6505465] using wordTrace_append hprefix tailTrace_6505465
  have hstable : (prefixWord ++ tailWord_6505465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505465).length < 2 ^ (prefixWord ++ tailWord_6505465).sum := by decide
  have hdescent : baseEnd_6505465 < baseStart_6505465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505488 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_6505488 : Nat := 118140960795 + 6505488 * 2 ^ 59
def prefixEnd_6505488 : Nat := 4983230072969 + 3 ^ 40 * 6505488 * 2
def baseEnd_6505488 : Nat := 3340442236056548481981811

theorem tailTrace_6505488 : CollatzResearch.WordTrace tailWord_6505488 prefixEnd_6505488 3340442236056548481981811 := by
  unfold tailWord_6505488
  simp only [CollatzResearch.WordTrace]
  refine ⟨118637320127867749870194559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158183093503823666493592745 118637320127867749870194559)
  ·
    refine ⟨177955980191801624805291839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118637320127867749870194559 177955980191801624805291839)
    ·
      refine ⟨266933970287702437207937759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177955980191801624805291839 266933970287702437207937759)
      ·
        refine ⟨400400955431553655811906639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266933970287702437207937759 400400955431553655811906639)
        ·
          refine ⟨600601433147330483717859959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400400955431553655811906639 600601433147330483717859959)
          ·
            refine ⟨900902149720995725576789939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600601433147330483717859959 900902149720995725576789939)
            ·
              refine ⟨1351353224581493588365184909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900902149720995725576789939 1351353224581493588365184909)
              ·
                refine ⟨506757459218060095636944341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1351353224581493588365184909 506757459218060095636944341)
                ·
                  refine ⟨11877127950423283491490883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 506757459218060095636944341 11877127950423283491490883)
                  ·
                    refine ⟨17815691925634925237236325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11877127950423283491490883 17815691925634925237236325)
                    ·
                      refine ⟨3340442236056548481981811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17815691925634925237236325 3340442236056548481981811)
                      ·
                        rfl

theorem cell23_6505488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_6505488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505488 prefixEnd_6505488 := by exact prefixLift 6505488
  have htrace : WordTrace (prefixWord ++ tailWord_6505488) baseStart_6505488 baseEnd_6505488 := by
    simpa [prefixWord, tailWord_6505488, baseEnd_6505488] using wordTrace_append hprefix tailTrace_6505488
  have hstable : (prefixWord ++ tailWord_6505488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505488).length < 2 ^ (prefixWord ++ tailWord_6505488).sum := by decide
  have hdescent : baseEnd_6505488 < baseStart_6505488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505498 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_6505498 : Nat := 118140960795 + 6505498 * 2 ^ 59
def prefixEnd_6505498 : Nat := 4983230072969 + 3 ^ 40 * 6505498 * 2
def baseEnd_6505498 : Nat := 1113482456954364480952255

theorem tailTrace_6505498 : CollatzResearch.WordTrace tailWord_6505498 prefixEnd_6505498 1113482456954364480952255 := by
  unfold tailWord_6505498
  simp only [CollatzResearch.WordTrace]
  refine ⟨59318751246424817862063287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158183336657132847632168765 59318751246424817862063287)
  ·
    refine ⟨88978126869637226793094931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59318751246424817862063287 88978126869637226793094931)
    ·
      refine ⟨133467190304455840189642397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88978126869637226793094931 133467190304455840189642397)
      ·
        refine ⟨50050196364170940071115899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133467190304455840189642397 50050196364170940071115899)
        ·
          refine ⟨75075294546256410106673849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50050196364170940071115899 75075294546256410106673849)
          ·
            refine ⟨56306470909692307580005387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75075294546256410106673849 56306470909692307580005387)
            ·
              refine ⟨84459706364538461370008081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56306470909692307580005387 84459706364538461370008081)
              ·
                refine ⟨63344779773403846027506061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84459706364538461370008081 63344779773403846027506061)
                ·
                  refine ⟨23754292415026442260314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63344779773403846027506061 23754292415026442260314773)
                  ·
                    refine ⟨1113482456954364480952255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23754292415026442260314773 1113482456954364480952255)
                    ·
                      rfl

theorem cell23_6505498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_6505498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505498 prefixEnd_6505498 := by exact prefixLift 6505498
  have htrace : WordTrace (prefixWord ++ tailWord_6505498) baseStart_6505498 baseEnd_6505498 := by
    simpa [prefixWord, tailWord_6505498, baseEnd_6505498] using wordTrace_append hprefix tailTrace_6505498
  have hstable : (prefixWord ++ tailWord_6505498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505498).length < 2 ^ (prefixWord ++ tailWord_6505498).sum := by decide
  have hdescent : baseEnd_6505498 < baseStart_6505498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505505 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6505505 : Nat := 118140960795 + 6505505 * 2 ^ 59
def prefixEnd_6505505 : Nat := 4983230072969 + 3 ^ 40 * 6505505 * 2
def baseEnd_6505505 : Nat := 3340450965227674915469233

theorem tailTrace_6505505 : CollatzResearch.WordTrace tailWord_6505505 prefixEnd_6505505 3340450965227674915469233 := by
  unfold tailWord_6505505
  simp only [CollatzResearch.WordTrace]
  refine ⟨237275260296673911643757969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158183506864449274429171979 237275260296673911643757969)
  ·
    refine ⟨177956445222505433732818477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237275260296673911643757969 177956445222505433732818477)
    ·
      refine ⟨66733666958439537649806929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177956445222505433732818477 66733666958439537649806929)
      ·
        refine ⟨50050250218829653237355197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66733666958439537649806929 50050250218829653237355197)
        ·
          refine ⟨18768843832061119964008199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50050250218829653237355197 18768843832061119964008199)
          ·
            refine ⟨28153265748091679946012299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18768843832061119964008199 28153265748091679946012299)
            ·
              refine ⟨42229898622137519919018449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28153265748091679946012299 42229898622137519919018449)
              ·
                refine ⟨31672423966603139939263837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42229898622137519919018449 31672423966603139939263837)
                ·
                  refine ⟨11877158987476177477223939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31672423966603139939263837 11877158987476177477223939)
                  ·
                    refine ⟨17815738481214266215835909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11877158987476177477223939 17815738481214266215835909)
                    ·
                      refine ⟨3340450965227674915469233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17815738481214266215835909 3340450965227674915469233)
                      ·
                        rfl

theorem cell23_6505505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6505505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505505 prefixEnd_6505505 := by exact prefixLift 6505505
  have htrace : WordTrace (prefixWord ++ tailWord_6505505) baseStart_6505505 baseEnd_6505505 := by
    simpa [prefixWord, tailWord_6505505, baseEnd_6505505] using wordTrace_append hprefix tailTrace_6505505
  have hstable : (prefixWord ++ tailWord_6505505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505505).length < 2 ^ (prefixWord ++ tailWord_6505505).sum := by decide
  have hdescent : baseEnd_6505505 < baseStart_6505505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505515 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 2, 4]
def baseStart_6505515 : Nat := 118140960795 + 6505515 * 2 ^ 59
def prefixEnd_6505515 : Nat := 4983230072969 + 3 ^ 40 * 6505515 * 2
def baseEnd_6505515 : Nat := 1113485366678073292114729

theorem tailTrace_6505515 : CollatzResearch.WordTrace tailWord_6505515 prefixEnd_6505515 1113485366678073292114729 := by
  unfold tailWord_6505515
  simp only [CollatzResearch.WordTrace]
  refine ⟨237275625026637683351621999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158183750017758455567747999 237275625026637683351621999)
  ·
    refine ⟨355913437539956525027432999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237275625026637683351621999 355913437539956525027432999)
    ·
      refine ⟨533870156309934787541149499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355913437539956525027432999 533870156309934787541149499)
      ·
        refine ⟨800805234464902181311724249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533870156309934787541149499 800805234464902181311724249)
        ·
          refine ⟨600603925848676635983793187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800805234464902181311724249 600603925848676635983793187)
          ·
            refine ⟨900905888773014953975689781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600603925848676635983793187 900905888773014953975689781)
            ·
              refine ⟨84459927072470151935220917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 900905888773014953975689781 84459927072470151935220917)
              ·
                refine ⟨7918118163044076743926961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84459927072470151935220917 7918118163044076743926961)
                ·
                  refine ⟨5938588622283057557945221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7918118163044076743926961 5938588622283057557945221)
                  ·
                    refine ⟨1113485366678073292114729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938588622283057557945221 1113485366678073292114729)
                    ·
                      rfl

theorem cell23_6505515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 4].length) (baseStart_6505515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505515 prefixEnd_6505515 := by exact prefixLift 6505515
  have htrace : WordTrace (prefixWord ++ tailWord_6505515) baseStart_6505515 baseEnd_6505515 := by
    simpa [prefixWord, tailWord_6505515, baseEnd_6505515] using wordTrace_append hprefix tailTrace_6505515
  have hstable : (prefixWord ++ tailWord_6505515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505515).length < 2 ^ (prefixWord ++ tailWord_6505515).sum := by decide
  have hdescent : baseEnd_6505515 < baseStart_6505515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505526 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6505526 : Nat := 118140960795 + 6505526 * 2 ^ 59
def prefixEnd_6505526 : Nat := 4983230072969 + 3 ^ 40 * 6505526 * 2
def baseEnd_6505526 : Nat := 3340461748321419333306637

theorem tailTrace_6505526 : CollatzResearch.WordTrace tailWord_6505526 prefixEnd_6505526 3340461748321419333306637 := by
  unfold tailWord_6505526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829751639349864514392027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158184017486398554820181621 14829751639349864514392027)
  ·
    refine ⟨22244627459024796771588041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14829751639349864514392027 22244627459024796771588041)
    ·
      refine ⟨16683470594268597578691031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22244627459024796771588041 16683470594268597578691031)
      ·
        refine ⟨25025205891402896368036547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16683470594268597578691031 25025205891402896368036547)
        ·
          refine ⟨37537808837104344552054821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25025205891402896368036547 37537808837104344552054821)
          ·
            refine ⟨7038339156957064603510279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37537808837104344552054821 7038339156957064603510279)
            ·
              refine ⟨10557508735435596905265419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038339156957064603510279 10557508735435596905265419)
              ·
                refine ⟨15836263103153395357898129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10557508735435596905265419 15836263103153395357898129)
                ·
                  refine ⟨11877197327365046518423597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15836263103153395357898129 11877197327365046518423597)
                  ·
                    refine ⟨4453948997761892444408849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11877197327365046518423597 4453948997761892444408849)
                    ·
                      refine ⟨3340461748321419333306637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453948997761892444408849 3340461748321419333306637)
                      ·
                        rfl

theorem cell23_6505526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6505526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505526 prefixEnd_6505526 := by exact prefixLift 6505526
  have htrace : WordTrace (prefixWord ++ tailWord_6505526) baseStart_6505526 baseEnd_6505526 := by
    simpa [prefixWord, tailWord_6505526, baseEnd_6505526] using wordTrace_append hprefix tailTrace_6505526
  have hstable : (prefixWord ++ tailWord_6505526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505526).length < 2 ^ (prefixWord ++ tailWord_6505526).sum := by decide
  have hdescent : baseEnd_6505526 < baseStart_6505526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505548 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6505548 : Nat := 118140960795 + 6505548 * 2 ^ 59
def prefixEnd_6505548 : Nat := 4983230072969 + 3 ^ 40 * 6505548 * 2
def baseEnd_6505548 : Nat := 3340473044895818247231535

theorem tailTrace_6505548 : CollatzResearch.WordTrace tailWord_6505548 prefixEnd_6505548 3340473044895818247231535 := by
  unfold tailWord_6505548
  simp only [CollatzResearch.WordTrace]
  refine ⟨118638414317759064993786649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158184552423678753325048865 118638414317759064993786649)
  ·
    refine ⟨88978810738319298745339987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118638414317759064993786649 88978810738319298745339987)
    ·
      refine ⟨133468216107478948118009981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88978810738319298745339987 133468216107478948118009981)
      ·
        refine ⟨50050581040304605544253743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133468216107478948118009981 50050581040304605544253743)
        ·
          refine ⟨75075871560456908316380615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50050581040304605544253743 75075871560456908316380615)
          ·
            refine ⟨112613807340685362474570923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75075871560456908316380615 112613807340685362474570923)
            ·
              refine ⟨168920711011028043711856385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112613807340685362474570923 168920711011028043711856385)
              ·
                refine ⟨126690533258271032783892289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168920711011028043711856385 126690533258271032783892289)
                ·
                  refine ⟨95017899943703274587919217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126690533258271032783892289 95017899943703274587919217)
                  ·
                    refine ⟨71263424957777455940939413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95017899943703274587919217 71263424957777455940939413)
                    ·
                      refine ⟨3340473044895818247231535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71263424957777455940939413 3340473044895818247231535)
                      ·
                        rfl

theorem cell23_6505548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6505548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505548 prefixEnd_6505548 := by exact prefixLift 6505548
  have htrace : WordTrace (prefixWord ++ tailWord_6505548) baseStart_6505548 baseEnd_6505548 := by
    simpa [prefixWord, tailWord_6505548, baseEnd_6505548] using wordTrace_append hprefix tailTrace_6505548
  have hstable : (prefixWord ++ tailWord_6505548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505548).length < 2 ^ (prefixWord ++ tailWord_6505548).sum := by decide
  have hdescent : baseEnd_6505548 < baseStart_6505548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505549 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6505549 : Nat := 118140960795 + 6505549 * 2 ^ 59
def prefixEnd_6505549 : Nat := 4983230072969 + 3 ^ 40 * 6505549 * 2
def baseEnd_6505549 : Nat := 1113491186125490914439677

theorem tailTrace_6505549 : CollatzResearch.WordTrace tailWord_6505549 prefixEnd_6505549 1113491186125490914439677 := by
  unfold tailWord_6505549
  simp only [CollatzResearch.WordTrace]
  refine ⟨237276865108514507158359701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158184576739009671438906467 237276865108514507158359701)
  ·
    refine ⟨11122353051961617523048111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237276865108514507158359701 11122353051961617523048111)
    ·
      refine ⟨16683529577942426284572167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11122353051961617523048111 16683529577942426284572167)
      ·
        refine ⟨25025294366913639426858251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16683529577942426284572167 25025294366913639426858251)
        ·
          refine ⟨37537941550370459140287377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25025294366913639426858251 37537941550370459140287377)
          ·
            refine ⟨28153456162777844355215533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37537941550370459140287377 28153456162777844355215533)
            ·
              refine ⟨10557546061041691633205825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28153456162777844355215533 10557546061041691633205825)
              ·
                refine ⟨7918159545781268724904369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10557546061041691633205825 7918159545781268724904369)
                ·
                  refine ⟨5938619659335951543678277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7918159545781268724904369 5938619659335951543678277)
                  ·
                    refine ⟨1113491186125490914439677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938619659335951543678277 1113491186125490914439677)
                    ·
                      rfl

theorem cell23_6505549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6505549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505549 prefixEnd_6505549 := by exact prefixLift 6505549
  have htrace : WordTrace (prefixWord ++ tailWord_6505549) baseStart_6505549 baseEnd_6505549 := by
    simpa [prefixWord, tailWord_6505549, baseEnd_6505549] using wordTrace_append hprefix tailTrace_6505549
  have hstable : (prefixWord ++ tailWord_6505549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505549).length < 2 ^ (prefixWord ++ tailWord_6505549).sum := by decide
  have hdescent : baseEnd_6505549 < baseStart_6505549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505556 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_6505556 : Nat := 118140960795 + 6505556 * 2 ^ 59
def prefixEnd_6505556 : Nat := 4983230072969 + 3 ^ 40 * 6505556 * 2
def baseEnd_6505556 : Nat := 3340477152741054215931499

theorem tailTrace_6505556 : CollatzResearch.WordTrace tailWord_6505556 prefixEnd_6505556 3340477152741054215931499 := by
  unfold tailWord_6505556
  simp only [CollatzResearch.WordTrace]
  refine ⟨118638560209744573676932261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158184746946326098235909681 118638560209744573676932261)
  ·
    refine ⟨22244730039327107564424799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118638560209744573676932261 22244730039327107564424799)
    ·
      refine ⟨33367095058990661346637199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22244730039327107564424799 33367095058990661346637199)
      ·
        refine ⟨50050642588485992019955799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33367095058990661346637199 50050642588485992019955799)
        ·
          refine ⟨75075963882728988029933699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50050642588485992019955799 75075963882728988029933699)
          ·
            refine ⟨112613945824093482044900549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75075963882728988029933699 112613945824093482044900549)
            ·
              refine ⟨21115114842017527883418853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112613945824093482044900549 21115114842017527883418853)
              ·
                refine ⟨3959084032878286478141035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21115114842017527883418853 3959084032878286478141035)
                ·
                  refine ⟨5938626049317429717211553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959084032878286478141035 5938626049317429717211553)
                  ·
                    refine ⟨4453969536988072287908665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5938626049317429717211553 4453969536988072287908665)
                    ·
                      refine ⟨3340477152741054215931499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4453969536988072287908665 3340477152741054215931499)
                      ·
                        rfl

theorem cell23_6505556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_6505556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505556 prefixEnd_6505556 := by exact prefixLift 6505556
  have htrace : WordTrace (prefixWord ++ tailWord_6505556) baseStart_6505556 baseEnd_6505556 := by
    simpa [prefixWord, tailWord_6505556, baseEnd_6505556] using wordTrace_append hprefix tailTrace_6505556
  have hstable : (prefixWord ++ tailWord_6505556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505556).length < 2 ^ (prefixWord ++ tailWord_6505556).sum := by decide
  have hdescent : baseEnd_6505556 < baseStart_6505556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505566 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6505566 : Nat := 118140960795 + 6505566 * 2 ^ 59
def prefixEnd_6505566 : Nat := 4983230072969 + 3 ^ 40 * 6505566 * 2
def baseEnd_6505566 : Nat := 1113494095849199725602151

theorem tailTrace_6505566 : CollatzResearch.WordTrace tailWord_6505566 prefixEnd_6505566 1113494095849199725602151 := by
  unfold tailWord_6505566
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659685643681614882716069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158184990099635279374485701 29659685643681614882716069)
  ·
    refine ⟨5561191058190302790509263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29659685643681614882716069 5561191058190302790509263)
    ·
      refine ⟨8341786587285454185763895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561191058190302790509263 8341786587285454185763895)
      ·
        refine ⟨12512679880928181278645843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8341786587285454185763895 12512679880928181278645843)
        ·
          refine ⟨18769019821392271917968765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512679880928181278645843 18769019821392271917968765)
          ·
            refine ⟨7038382433022101969238287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18769019821392271917968765 7038382433022101969238287)
            ·
              refine ⟨10557573649533152953857431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038382433022101969238287 10557573649533152953857431)
              ·
                refine ⟨15836360474299729430786147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10557573649533152953857431 15836360474299729430786147)
                ·
                  refine ⟨23754540711449594146179221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15836360474299729430786147 23754540711449594146179221)
                  ·
                    refine ⟨1113494095849199725602151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23754540711449594146179221 1113494095849199725602151)
                    ·
                      rfl

theorem cell23_6505566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6505566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505566 prefixEnd_6505566 := by exact prefixLift 6505566
  have htrace : WordTrace (prefixWord ++ tailWord_6505566) baseStart_6505566 baseEnd_6505566 := by
    simpa [prefixWord, tailWord_6505566, baseEnd_6505566] using wordTrace_append hprefix tailTrace_6505566
  have hstable : (prefixWord ++ tailWord_6505566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505566).length < 2 ^ (prefixWord ++ tailWord_6505566).sum := by decide
  have hdescent : baseEnd_6505566 < baseStart_6505566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505576 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6505576 : Nat := 118140960795 + 6505576 * 2 ^ 59
def prefixEnd_6505576 : Nat := 4983230072969 + 3 ^ 40 * 6505576 * 2
def baseEnd_6505576 : Nat := 3340487422354144137681407

theorem tailTrace_6505576 : CollatzResearch.WordTrace tailWord_6505576 prefixEnd_6505576 3340487422354144137681407 := by
  unfold tailWord_6505576
  simp only [CollatzResearch.WordTrace]
  refine ⟨118638924939708345384796291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158185233252944460513061721 118638924939708345384796291)
  ·
    refine ⟨177958387409562518077194437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118638924939708345384796291 177958387409562518077194437)
    ·
      refine ⟨33367197639292972139473957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177958387409562518077194437 33367197639292972139473957)
      ·
        refine ⟨6256349557367432276151367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33367197639292972139473957 6256349557367432276151367)
        ·
          refine ⟨9384524336051148414227051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256349557367432276151367 9384524336051148414227051)
          ·
            refine ⟨14076786504076722621340577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9384524336051148414227051 14076786504076722621340577)
            ·
              refine ⟨10557589878057541966005433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14076786504076722621340577 10557589878057541966005433)
              ·
                refine ⟨7918192408543156474504075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10557589878057541966005433 7918192408543156474504075)
                ·
                  refine ⟨11877288612814734711756113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918192408543156474504075 11877288612814734711756113)
                  ·
                    refine ⟨8907966459611051033817085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11877288612814734711756113 8907966459611051033817085)
                    ·
                      refine ⟨3340487422354144137681407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8907966459611051033817085 3340487422354144137681407)
                      ·
                        rfl

theorem cell23_6505576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6505576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505576 prefixEnd_6505576 := by exact prefixLift 6505576
  have htrace : WordTrace (prefixWord ++ tailWord_6505576) baseStart_6505576 baseEnd_6505576 := by
    simpa [prefixWord, tailWord_6505576, baseEnd_6505576] using wordTrace_append hprefix tailTrace_6505576
  have hstable : (prefixWord ++ tailWord_6505576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505576).length < 2 ^ (prefixWord ++ tailWord_6505576).sum := by decide
  have hdescent : baseEnd_6505576 < baseStart_6505576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505672 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_6505672 : Nat := 118140960795 + 6505672 * 2 ^ 59
def prefixEnd_6505672 : Nat := 4983230072969 + 3 ^ 40 * 6505672 * 2
def baseEnd_6505672 : Nat := 3340536716496975762080965

theorem tailTrace_6505672 : CollatzResearch.WordTrace tailWord_6505672 prefixEnd_6505672 3340536716496975762080965 := by
  unfold tailWord_6505672
  simp only [CollatzResearch.WordTrace]
  refine ⟨118640675643534449582543635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158187567524712599443391513 118640675643534449582543635)
  ·
    refine ⟨177961013465301674373815453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118640675643534449582543635 177961013465301674373815453)
    ·
      refine ⟨66735380049488127890180795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177961013465301674373815453 66735380049488127890180795)
      ·
        refine ⟨100103070074232191835271193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66735380049488127890180795 100103070074232191835271193)
        ·
          refine ⟨75077302555674143876453395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100103070074232191835271193 75077302555674143876453395)
          ·
            refine ⟨112615953833511215814680093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75077302555674143876453395 112615953833511215814680093)
            ·
              refine ⟨42230982687566705930505035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112615953833511215814680093 42230982687566705930505035)
              ·
                refine ⟨63346474031350058895757553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42230982687566705930505035 63346474031350058895757553)
                ·
                  refine ⟨47509855523512544171818165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63346474031350058895757553 47509855523512544171818165)
                  ·
                    refine ⟨4454048955329301016107953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47509855523512544171818165 4454048955329301016107953)
                    ·
                      refine ⟨3340536716496975762080965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454048955329301016107953 3340536716496975762080965)
                      ·
                        rfl

theorem cell23_6505672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_6505672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505672 prefixEnd_6505672 := by exact prefixLift 6505672
  have htrace : WordTrace (prefixWord ++ tailWord_6505672) baseStart_6505672 baseEnd_6505672 := by
    simpa [prefixWord, tailWord_6505672, baseEnd_6505672] using wordTrace_append hprefix tailTrace_6505672
  have hstable : (prefixWord ++ tailWord_6505672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505672).length < 2 ^ (prefixWord ++ tailWord_6505672).sum := by decide
  have hdescent : baseEnd_6505672 < baseStart_6505672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505715 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_6505715 : Nat := 118140960795 + 6505715 * 2 ^ 59
def prefixEnd_6505715 : Nat := 4983230072969 + 3 ^ 40 * 6505715 * 2
def baseEnd_6505715 : Nat := 3340558796165119093843267

theorem tailTrace_6505715 : CollatzResearch.WordTrace tailWord_6505715 prefixEnd_6505715 3340558796165119093843267 := by
  unfold tailWord_6505715
  simp only [CollatzResearch.WordTrace]
  refine ⟨237282919625913117508902599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158188613083942078339268399 237282919625913117508902599)
  ·
    refine ⟨355924379438869676263353899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237282919625913117508902599 355924379438869676263353899)
    ·
      refine ⟨533886569158304514395030849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355924379438869676263353899 533886569158304514395030849)
      ·
        refine ⟨400414926868728385796273137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533886569158304514395030849 400414926868728385796273137)
        ·
          refine ⟨300311195151546289347204853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400414926868728385796273137 300311195151546289347204853)
          ·
            refine ⟨28154174545457464626300455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300311195151546289347204853 28154174545457464626300455)
            ·
              refine ⟨42231261818186196939450683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28154174545457464626300455 42231261818186196939450683)
              ·
                refine ⟨63346892727279295409176025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42231261818186196939450683 63346892727279295409176025)
                ·
                  refine ⟨47510169545459471556882019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63346892727279295409176025 47510169545459471556882019)
                  ·
                    refine ⟨71265254318189207335323029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47510169545459471556882019 71265254318189207335323029)
                    ·
                      refine ⟨3340558796165119093843267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71265254318189207335323029 3340558796165119093843267)
                      ·
                        rfl

theorem cell23_6505715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_6505715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505715 prefixEnd_6505715 := by exact prefixLift 6505715
  have htrace : WordTrace (prefixWord ++ tailWord_6505715) baseStart_6505715 baseEnd_6505715 := by
    simpa [prefixWord, tailWord_6505715, baseEnd_6505715] using wordTrace_append hprefix tailTrace_6505715
  have hstable : (prefixWord ++ tailWord_6505715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505715).length < 2 ^ (prefixWord ++ tailWord_6505715).sum := by decide
  have hdescent : baseEnd_6505715 < baseStart_6505715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505722 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_6505722 : Nat := 118140960795 + 6505722 * 2 ^ 59
def prefixEnd_6505722 : Nat := 4983230072969 + 3 ^ 40 * 6505722 * 2
def baseEnd_6505722 : Nat := 3340562390529700566455735

theorem tailTrace_6505722 : CollatzResearch.WordTrace tailWord_6505722 prefixEnd_6505722 3340562390529700566455735 := by
  unfold tailWord_6505722
  simp only [CollatzResearch.WordTrace]
  refine ⟨59320793734221939426101855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158188783291258505136271613 59320793734221939426101855)
  ·
    refine ⟨88981190601332909139152783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59320793734221939426101855 88981190601332909139152783)
    ·
      refine ⟨133471785901999363708729175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88981190601332909139152783 133471785901999363708729175)
      ·
        refine ⟨200207678852999045563093763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133471785901999363708729175 200207678852999045563093763)
        ·
          refine ⟨300311518279498568344640645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200207678852999045563093763 300311518279498568344640645)
          ·
            refine ⟨56308409677405981564620121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300311518279498568344640645 56308409677405981564620121)
            ·
              refine ⟨42231307258054486173465091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56308409677405981564620121 42231307258054486173465091)
              ·
                refine ⟨63346960887081729260197637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42231307258054486173465091 63346960887081729260197637)
                ·
                  refine ⟨11877555166327824236287057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63346960887081729260197637 11877555166327824236287057)
                  ·
                    refine ⟨8908166374745868177215293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11877555166327824236287057 8908166374745868177215293)
                    ·
                      refine ⟨3340562390529700566455735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908166374745868177215293 3340562390529700566455735)
                      ·
                        rfl

theorem cell23_6505722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_6505722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505722 prefixEnd_6505722 := by exact prefixLift 6505722
  have htrace : WordTrace (prefixWord ++ tailWord_6505722) baseStart_6505722 baseEnd_6505722 := by
    simpa [prefixWord, tailWord_6505722, baseEnd_6505722] using wordTrace_append hprefix tailTrace_6505722
  have hstable : (prefixWord ++ tailWord_6505722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505722).length < 2 ^ (prefixWord ++ tailWord_6505722).sum := by decide
  have hdescent : baseEnd_6505722 < baseStart_6505722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505729 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_6505729 : Nat := 118140960795 + 6505729 * 2 ^ 59
def prefixEnd_6505729 : Nat := 4983230072969 + 3 ^ 40 * 6505729 * 2
def baseEnd_6505729 : Nat := 1113521994964760679689401

theorem tailTrace_6505729 : CollatzResearch.WordTrace tailWord_6505729 prefixEnd_6505729 1113521994964760679689401 := by
  unfold tailWord_6505729
  simp only [CollatzResearch.WordTrace]
  refine ⟨237283430247862397899912241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158188953498574931933274827 237283430247862397899912241)
  ·
    refine ⟨177962572685896798424934181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237283430247862397899912241 177962572685896798424934181)
    ·
      refine ⟨33367982378605649704675159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177962572685896798424934181 33367982378605649704675159)
      ·
        refine ⟨50051973567908474557012739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33367982378605649704675159 50051973567908474557012739)
        ·
          refine ⟨75077960351862711835519109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50051973567908474557012739 75077960351862711835519109)
          ·
            refine ⟨14077117565974258469159833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75077960351862711835519109 14077117565974258469159833)
            ·
              refine ⟨10557838174480693851869875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14077117565974258469159833 10557838174480693851869875)
              ·
                refine ⟨15836757261721040777804813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10557838174480693851869875 15836757261721040777804813)
                ·
                  refine ⟨5938783973145390291676805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15836757261721040777804813 5938783973145390291676805)
                  ·
                    refine ⟨1113521994964760679689401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938783973145390291676805 1113521994964760679689401)
                    ·
                      rfl

theorem cell23_6505729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_6505729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505729 prefixEnd_6505729 := by exact prefixLift 6505729
  have htrace : WordTrace (prefixWord ++ tailWord_6505729) baseStart_6505729 baseEnd_6505729 := by
    simpa [prefixWord, tailWord_6505729, baseEnd_6505729] using wordTrace_append hprefix tailTrace_6505729
  have hstable : (prefixWord ++ tailWord_6505729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505729).length < 2 ^ (prefixWord ++ tailWord_6505729).sum := by decide
  have hdescent : baseEnd_6505729 < baseStart_6505729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505745 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_6505745 : Nat := 118140960795 + 6505745 * 2 ^ 59
def prefixEnd_6505745 : Nat := 4983230072969 + 3 ^ 40 * 6505745 * 2
def baseEnd_6505745 : Nat := 3340574200584753976468129

theorem tailTrace_6505745 : CollatzResearch.WordTrace tailWord_6505745 prefixEnd_6505745 3340574200584753976468129 := by
  unfold tailWord_6505745
  simp only [CollatzResearch.WordTrace]
  refine ⟨237284013815804432632494689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158189342543869621754996459 237284013815804432632494689)
  ·
    refine ⟨177963010361853324474371017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237284013815804432632494689 177963010361853324474371017)
    ·
      refine ⟨133472257771389993355778263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177963010361853324474371017 133472257771389993355778263)
      ·
        refine ⟨200208386657084990033667395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133472257771389993355778263 200208386657084990033667395)
        ·
          refine ⟨300312579985627485050501093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200208386657084990033667395 300312579985627485050501093)
          ·
            refine ⟨56308608747305153446968955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300312579985627485050501093 56308608747305153446968955)
            ·
              refine ⟨84462913120957730170453433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56308608747305153446968955 84462913120957730170453433)
              ·
                refine ⟨63347184840718297627840075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84462913120957730170453433 63347184840718297627840075)
                ·
                  refine ⟨95020777261077446441760113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63347184840718297627840075 95020777261077446441760113)
                  ·
                    refine ⟨71265582945808084831320085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95020777261077446441760113 71265582945808084831320085)
                    ·
                      refine ⟨3340574200584753976468129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71265582945808084831320085 3340574200584753976468129)
                      ·
                        rfl

theorem cell23_6505745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_6505745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505745 prefixEnd_6505745 := by exact prefixLift 6505745
  have htrace : WordTrace (prefixWord ++ tailWord_6505745) baseStart_6505745 baseEnd_6505745 := by
    simpa [prefixWord, tailWord_6505745, baseEnd_6505745] using wordTrace_append hprefix tailTrace_6505745
  have hstable : (prefixWord ++ tailWord_6505745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505745).length < 2 ^ (prefixWord ++ tailWord_6505745).sum := by decide
  have hdescent : baseEnd_6505745 < baseStart_6505745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505779 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 4, 3, 2]
def baseStart_6505779 : Nat := 118140960795 + 6505779 * 2 ^ 59
def prefixEnd_6505779 : Nat := 4983230072969 + 3 ^ 40 * 6505779 * 2
def baseEnd_6505779 : Nat := 3340591658927006843442973

theorem tailTrace_6505779 : CollatzResearch.WordTrace tailWord_6505779 prefixEnd_6505779 3340591658927006843442973 := by
  unfold tailWord_6505779
  simp only [CollatzResearch.WordTrace]
  refine ⟨237285253897681256439232391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158190169265120837626154927 237285253897681256439232391)
  ·
    refine ⟨355927880846521884658848587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237285253897681256439232391 355927880846521884658848587)
    ·
      refine ⟨533891821269782826988272881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355927880846521884658848587 533891821269782826988272881)
      ·
        refine ⟨400418865952337120241204661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533891821269782826988272881 400418865952337120241204661)
        ·
          refine ⟨37539268683031605022612937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400418865952337120241204661 37539268683031605022612937)
          ·
            refine ⟨28154451512273703766959703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37539268683031605022612937 28154451512273703766959703)
            ·
              refine ⟨42231677268410555650439555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28154451512273703766959703 42231677268410555650439555)
              ·
                refine ⟨63347515902615833475659333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42231677268410555650439555 63347515902615833475659333)
                ·
                  refine ⟨11877659231740468776686125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63347515902615833475659333 11877659231740468776686125)
                  ·
                    refine ⟨4454122211902675791257297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11877659231740468776686125 4454122211902675791257297)
                    ·
                      refine ⟨3340591658927006843442973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454122211902675791257297 3340591658927006843442973)
                      ·
                        rfl

theorem cell23_6505779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 3, 2].length) (baseStart_6505779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505779 prefixEnd_6505779 := by exact prefixLift 6505779
  have htrace : WordTrace (prefixWord ++ tailWord_6505779) baseStart_6505779 baseEnd_6505779 := by
    simpa [prefixWord, tailWord_6505779, baseEnd_6505779] using wordTrace_append hprefix tailTrace_6505779
  have hstable : (prefixWord ++ tailWord_6505779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505779).length < 2 ^ (prefixWord ++ tailWord_6505779).sum := by decide
  have hdescent : baseEnd_6505779 < baseStart_6505779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505792 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_6505792 : Nat := 118140960795 + 6505792 * 2 ^ 59
def prefixEnd_6505792 : Nat := 4983230072969 + 3 ^ 40 * 6505792 * 2
def baseEnd_6505792 : Nat := 3340598334175515292580413

theorem tailTrace_6505792 : CollatzResearch.WordTrace tailWord_6505792 prefixEnd_6505792 3340598334175515292580413 := by
  unfold tailWord_6505792
  simp only [CollatzResearch.WordTrace]
  refine ⟨118642864023317079829727815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158190485364422773106303753 118642864023317079829727815)
  ·
    refine ⟨177964296034975619744591723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118642864023317079829727815 177964296034975619744591723)
    ·
      refine ⟨266946444052463429616887585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177964296034975619744591723 266946444052463429616887585)
      ·
        refine ⟨200209833039347572212665689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266946444052463429616887585 200209833039347572212665689)
        ·
          refine ⟨150157374779510679159499267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200209833039347572212665689 150157374779510679159499267)
          ·
            refine ⟨225236062169266018739248901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150157374779510679159499267 225236062169266018739248901)
            ·
              refine ⟨42231761656737378513609169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225236062169266018739248901 42231761656737378513609169)
              ·
                refine ⟨31673821242553033885206877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42231761656737378513609169 31673821242553033885206877)
                ·
                  refine ⟨11877682965957387706952579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31673821242553033885206877 11877682965957387706952579)
                  ·
                    refine ⟨17816524448936081560428869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11877682965957387706952579 17816524448936081560428869)
                    ·
                      refine ⟨3340598334175515292580413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17816524448936081560428869 3340598334175515292580413)
                      ·
                        rfl

theorem cell23_6505792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_6505792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505792 prefixEnd_6505792 := by exact prefixLift 6505792
  have htrace : WordTrace (prefixWord ++ tailWord_6505792) baseStart_6505792 baseEnd_6505792 := by
    simpa [prefixWord, tailWord_6505792, baseEnd_6505792] using wordTrace_append hprefix tailTrace_6505792
  have hstable : (prefixWord ++ tailWord_6505792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505792).length < 2 ^ (prefixWord ++ tailWord_6505792).sum := by decide
  have hdescent : baseEnd_6505792 < baseStart_6505792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505832 : List Nat := [2, 1, 4, 2, 3, 11]
def baseStart_6505832 : Nat := 118140960795 + 6505832 * 2 ^ 59
def prefixEnd_6505832 : Nat := 4983230072969 + 3 ^ 40 * 6505832 * 2
def baseEnd_6505832 : Nat := 13747402771200391506503

theorem tailTrace_6505832 : CollatzResearch.WordTrace tailWord_6505832 prefixEnd_6505832 13747402771200391506503 := by
  unfold tailWord_6505832
  simp only [CollatzResearch.WordTrace]
  refine ⟨118643593483244623245455875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158191457977659497660607833 118643593483244623245455875)
  ·
    refine ⟨177965390224866934868183813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118643593483244623245455875 177965390224866934868183813)
    ·
      refine ⟨33368510667162550287784465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177965390224866934868183813 33368510667162550287784465)
      ·
        refine ⟨25026383000371912715838349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33368510667162550287784465 25026383000371912715838349)
        ·
          refine ⟨9384893625139467268439381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25026383000371912715838349 9384893625139467268439381)
          ·
            refine ⟨13747402771200391506503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9384893625139467268439381 13747402771200391506503)
            ·
              rfl

theorem cell23_6505832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 11].length) (baseStart_6505832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505832 prefixEnd_6505832 := by exact prefixLift 6505832
  have htrace : WordTrace (prefixWord ++ tailWord_6505832) baseStart_6505832 baseEnd_6505832 := by
    simpa [prefixWord, tailWord_6505832, baseEnd_6505832] using wordTrace_append hprefix tailTrace_6505832
  have hstable : (prefixWord ++ tailWord_6505832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505832).length < 2 ^ (prefixWord ++ tailWord_6505832).sum := by decide
  have hdescent : baseEnd_6505832 < baseStart_6505832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505836 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_6505836 : Nat := 118140960795 + 6505836 * 2 ^ 59
def prefixEnd_6505836 : Nat := 4983230072969 + 3 ^ 40 * 6505836 * 2
def baseEnd_6505836 : Nat := 1113540309108104373476737

theorem tailTrace_6505836 : CollatzResearch.WordTrace tailWord_6505836 prefixEnd_6505836 1113540309108104373476737 := by
  unfold tailWord_6505836
  simp only [CollatzResearch.WordTrace]
  refine ⟨118643666429237377587028681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158191555238983170116038241 118643666429237377587028681)
  ·
    refine ⟨88982749821928033190271511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118643666429237377587028681 88982749821928033190271511)
    ·
      refine ⟨133474124732892049785407267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88982749821928033190271511 133474124732892049785407267)
      ·
        refine ⟨200211187099338074678110901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133474124732892049785407267 200211187099338074678110901)
        ·
          refine ⟨18769798790562944501072897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200211187099338074678110901 18769798790562944501072897)
          ·
            refine ⟨14077349092922208375804673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18769798790562944501072897 14077349092922208375804673)
            ·
              refine ⟨10558011819691656281853505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14077349092922208375804673 10558011819691656281853505)
              ·
                refine ⟨7918508864768742211390129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10558011819691656281853505 7918508864768742211390129)
                ·
                  refine ⟨5938881648576556658542597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7918508864768742211390129 5938881648576556658542597)
                  ·
                    refine ⟨1113540309108104373476737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5938881648576556658542597 1113540309108104373476737)
                    ·
                      rfl

theorem cell23_6505836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_6505836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505836 prefixEnd_6505836 := by exact prefixLift 6505836
  have htrace : WordTrace (prefixWord ++ tailWord_6505836) baseStart_6505836 baseEnd_6505836 := by
    simpa [prefixWord, tailWord_6505836, baseEnd_6505836] using wordTrace_append hprefix tailTrace_6505836
  have hstable : (prefixWord ++ tailWord_6505836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505836).length < 2 ^ (prefixWord ++ tailWord_6505836).sum := by decide
  have hdescent : baseEnd_6505836 < baseStart_6505836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505859 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3]
def baseStart_6505859 : Nat := 118140960795 + 6505859 * 2 ^ 59
def prefixEnd_6505859 : Nat := 4983230072969 + 3 ^ 40 * 6505859 * 2
def baseEnd_6505859 : Nat := 3340632737379366530442605

theorem tailTrace_6505859 : CollatzResearch.WordTrace tailWord_6505859 prefixEnd_6505859 3340632737379366530442605 := by
  unfold tailWord_6505859
  simp only [CollatzResearch.WordTrace]
  refine ⟨237288171737391430102144631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158192114491594286734763087 237288171737391430102144631)
  ·
    refine ⟨355932257606087145153216947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237288171737391430102144631 355932257606087145153216947)
    ·
      refine ⟨533898386409130717729825421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355932257606087145153216947 533898386409130717729825421)
      ·
        refine ⟨200211894903424019148684533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533898386409130717729825421 200211894903424019148684533)
        ·
          refine ⟨18769865147196001795189175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200211894903424019148684533 18769865147196001795189175)
          ·
            refine ⟨28154797720794002692783763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18769865147196001795189175 28154797720794002692783763)
            ·
              refine ⟨42232196581191004039175645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28154797720794002692783763 42232196581191004039175645)
              ·
                refine ⟨15837073717946626514690867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42232196581191004039175645 15837073717946626514690867)
                ·
                  refine ⟨23755610576919939772036301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15837073717946626514690867 23755610576919939772036301)
                  ·
                    refine ⟨8908353966344977414513613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23755610576919939772036301 8908353966344977414513613)
                    ·
                      refine ⟨3340632737379366530442605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908353966344977414513613 3340632737379366530442605)
                      ·
                        rfl

theorem cell23_6505859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_6505859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505859 prefixEnd_6505859 := by exact prefixLift 6505859
  have htrace : WordTrace (prefixWord ++ tailWord_6505859) baseStart_6505859 baseEnd_6505859 := by
    simpa [prefixWord, tailWord_6505859, baseEnd_6505859] using wordTrace_append hprefix tailTrace_6505859
  have hstable : (prefixWord ++ tailWord_6505859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505859).length < 2 ^ (prefixWord ++ tailWord_6505859).sum := by decide
  have hdescent : baseEnd_6505859 < baseStart_6505859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505876 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_6505876 : Nat := 118140960795 + 6505876 * 2 ^ 59
def prefixEnd_6505876 : Nat := 4983230072969 + 3 ^ 40 * 6505876 * 2
def baseEnd_6505876 : Nat := 3340641466550492963930027

theorem tailTrace_6505876 : CollatzResearch.WordTrace tailWord_6505876 prefixEnd_6505876 3340641466550492963930027 := by
  unfold tailWord_6505876
  simp only [CollatzResearch.WordTrace]
  refine ⟨118644395889164921002756741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158192527852219894670342321 118644395889164921002756741)
  ·
    refine ⟨22245824229218422688016889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118644395889164921002756741 22245824229218422688016889)
    ·
      refine ⟨16684368171913817016012667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22245824229218422688016889 16684368171913817016012667)
      ·
        refine ⟨25026552257870725524019001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684368171913817016012667 25026552257870725524019001)
        ·
          refine ⟨18769914193403044143014251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25026552257870725524019001 18769914193403044143014251)
          ·
            refine ⟨28154871290104566214521377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18769914193403044143014251 28154871290104566214521377)
            ·
              refine ⟨21116153467578424660891033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28154871290104566214521377 21116153467578424660891033)
              ·
                refine ⟨15837115100683818495668275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21116153467578424660891033 15837115100683818495668275)
                ·
                  refine ⟨23755672651025727743502413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15837115100683818495668275 23755672651025727743502413)
                  ·
                    refine ⟨8908377244134647903813405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23755672651025727743502413 8908377244134647903813405)
                    ·
                      refine ⟨3340641466550492963930027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908377244134647903813405 3340641466550492963930027)
                      ·
                        rfl

theorem cell23_6505876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_6505876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505876 prefixEnd_6505876 := by exact prefixLift 6505876
  have htrace : WordTrace (prefixWord ++ tailWord_6505876) baseStart_6505876 baseEnd_6505876 := by
    simpa [prefixWord, tailWord_6505876, baseEnd_6505876] using wordTrace_append hprefix tailTrace_6505876
  have hstable : (prefixWord ++ tailWord_6505876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505876).length < 2 ^ (prefixWord ++ tailWord_6505876).sum := by decide
  have hdescent : baseEnd_6505876 < baseStart_6505876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505880 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6505880 : Nat := 118140960795 + 6505880 * 2 ^ 59
def prefixEnd_6505880 : Nat := 4983230072969 + 3 ^ 40 * 6505880 * 2
def baseEnd_6505880 : Nat := 3340643520473110948280009

theorem tailTrace_6505880 : CollatzResearch.WordTrace tailWord_6505880 prefixEnd_6505880 3340643520473110948280009 := by
  unfold tailWord_6505880
  simp only [CollatzResearch.WordTrace]
  refine ⟨118644468835157675344329547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158192625113543567125772729 118644468835157675344329547)
  ·
    refine ⟨177966703252736513016494321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118644468835157675344329547 177966703252736513016494321)
    ·
      refine ⟨133475027439552384762370741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177966703252736513016494321 133475027439552384762370741)
      ·
        refine ⟨12513283822458036071472257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133475027439552384762370741 12513283822458036071472257)
        ·
          refine ⟨9384962866843527053604193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12513283822458036071472257 9384962866843527053604193)
          ·
            refine ⟨7038722150132645290203145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9384962866843527053604193 7038722150132645290203145)
            ·
              refine ⟨5279041612599483967652359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7038722150132645290203145 5279041612599483967652359)
              ·
                refine ⟨7918562418899225951478539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279041612599483967652359 7918562418899225951478539)
                ·
                  refine ⟨11877843628348838927217809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918562418899225951478539 11877843628348838927217809)
                  ·
                    refine ⟨8908382721261629195413357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11877843628348838927217809 8908382721261629195413357)
                    ·
                      refine ⟨3340643520473110948280009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908382721261629195413357 3340643520473110948280009)
                      ·
                        rfl

theorem cell23_6505880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6505880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505880 prefixEnd_6505880 := by exact prefixLift 6505880
  have htrace : WordTrace (prefixWord ++ tailWord_6505880) baseStart_6505880 baseEnd_6505880 := by
    simpa [prefixWord, tailWord_6505880, baseEnd_6505880] using wordTrace_append hprefix tailTrace_6505880
  have hstable : (prefixWord ++ tailWord_6505880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505880).length < 2 ^ (prefixWord ++ tailWord_6505880).sum := by decide
  have hdescent : baseEnd_6505880 < baseStart_6505880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505909 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6505909 : Nat := 118140960795 + 6505909 * 2 ^ 59
def prefixEnd_6505909 : Nat := 4983230072969 + 3 ^ 40 * 6505909 * 2
def baseEnd_6505909 : Nat := 1113552803804030444939125

theorem tailTrace_6505909 : CollatzResearch.WordTrace tailWord_6505909 prefixEnd_6505909 1113552803804030444939125 := by
  unfold tailWord_6505909
  simp only [CollatzResearch.WordTrace]
  refine ⟨237289995387210288641464781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158193330258140192427643187 237289995387210288641464781)
  ·
    refine ⟨88983748270203858240549293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237289995387210288641464781 88983748270203858240549293)
    ·
      refine ⟨33368905601326446840205985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88983748270203858240549293 33368905601326446840205985)
      ·
        refine ⟨25026679200994835130154489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33368905601326446840205985 25026679200994835130154489)
        ·
          refine ⟨18770009400746126347615867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25026679200994835130154489 18770009400746126347615867)
          ·
            refine ⟨28155014101119189521423801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18770009400746126347615867 28155014101119189521423801)
            ·
              refine ⟨21116260575839392141067851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28155014101119189521423801 21116260575839392141067851)
              ·
                refine ⟨31674390863759088211601777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21116260575839392141067851 31674390863759088211601777)
                ·
                  refine ⟨23755793147819316158701333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31674390863759088211601777 23755793147819316158701333)
                  ·
                    refine ⟨1113552803804030444939125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23755793147819316158701333 1113552803804030444939125)
                    ·
                      rfl

theorem cell23_6505909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6505909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505909 prefixEnd_6505909 := by exact prefixLift 6505909
  have htrace : WordTrace (prefixWord ++ tailWord_6505909) baseStart_6505909 baseEnd_6505909 := by
    simpa [prefixWord, tailWord_6505909, baseEnd_6505909] using wordTrace_append hprefix tailTrace_6505909
  have hstable : (prefixWord ++ tailWord_6505909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505909).length < 2 ^ (prefixWord ++ tailWord_6505909).sum := by decide
  have hdescent : baseEnd_6505909 < baseStart_6505909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6505952 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_6505952 : Nat := 118140960795 + 6505952 * 2 ^ 59
def prefixEnd_6505952 : Nat := 4983230072969 + 3 ^ 40 * 6505952 * 2
def baseEnd_6505952 : Nat := 1113560163693411555526559

theorem tailTrace_6505952 : CollatzResearch.WordTrace tailWord_6505952 prefixEnd_6505952 1113560163693411555526559 := by
  unfold tailWord_6505952
  simp only [CollatzResearch.WordTrace]
  refine ⟨118645781863027253492640055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158194375817369671323520073 118645781863027253492640055)
  ·
    refine ⟨177968672794540880238960083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118645781863027253492640055 177968672794540880238960083)
    ·
      refine ⟨266953009191811320358440125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177968672794540880238960083 266953009191811320358440125)
      ·
        refine ⟨100107378446929245134415047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266953009191811320358440125 100107378446929245134415047)
        ·
          refine ⟨150161067670393867701622571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100107378446929245134415047 150161067670393867701622571)
          ·
            refine ⟨225241601505590801552433857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150161067670393867701622571 225241601505590801552433857)
            ·
              refine ⟨168931201129193101164325393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225241601505590801552433857 168931201129193101164325393)
              ·
                refine ⟨126698400846894825873244045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168931201129193101164325393 126698400846894825873244045)
                ·
                  refine ⟨47511900317585559702466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126698400846894825873244045 47511900317585559702466517)
                  ·
                    refine ⟨1113560163693411555526559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47511900317585559702466517 1113560163693411555526559)
                    ·
                      rfl

theorem cell23_6505952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_6505952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6505952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6505952 prefixEnd_6505952 := by exact prefixLift 6505952
  have htrace : WordTrace (prefixWord ++ tailWord_6505952) baseStart_6505952 baseEnd_6505952 := by
    simpa [prefixWord, tailWord_6505952, baseEnd_6505952] using wordTrace_append hprefix tailTrace_6505952
  have hstable : (prefixWord ++ tailWord_6505952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6505952).length < 2 ^ (prefixWord ++ tailWord_6505952).sum := by decide
  have hdescent : baseEnd_6505952 < baseStart_6505952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6505952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506026 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6506026 : Nat := 118140960795 + 6506026 * 2 ^ 59
def prefixEnd_6506026 : Nat := 4983230072969 + 3 ^ 40 * 6506026 * 2
def baseEnd_6506026 : Nat := 3340718488648667377054337

theorem tailTrace_6506026 : CollatzResearch.WordTrace tailWord_6506026 prefixEnd_6506026 3340718488648667377054337 := by
  unfold tailWord_6506026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59323565681946604405868483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158196175151857611748982621 59323565681946604405868483)
  ·
    refine ⟨88985348522919906608802725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59323565681946604405868483 88985348522919906608802725)
    ·
      refine ⟨16684752848047482489150511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88985348522919906608802725 16684752848047482489150511)
      ·
        refine ⟨25027129272071223733725767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684752848047482489150511 25027129272071223733725767)
        ·
          refine ⟨37540693908106835600588651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027129272071223733725767 37540693908106835600588651)
          ·
            refine ⟨56311040862160253400882977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37540693908106835600588651 56311040862160253400882977)
            ·
              refine ⟨42233280646620190050662233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56311040862160253400882977 42233280646620190050662233)
              ·
                refine ⟨31674960484965142537996675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42233280646620190050662233 31674960484965142537996675)
                ·
                  refine ⟨47512440727447713806995013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31674960484965142537996675 47512440727447713806995013)
                  ·
                    refine ⟨8908582636396446338811565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47512440727447713806995013 8908582636396446338811565)
                    ·
                      refine ⟨3340718488648667377054337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908582636396446338811565 3340718488648667377054337)
                      ·
                        rfl

theorem cell23_6506026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6506026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506026 prefixEnd_6506026 := by exact prefixLift 6506026
  have htrace : WordTrace (prefixWord ++ tailWord_6506026) baseStart_6506026 baseEnd_6506026 := by
    simpa [prefixWord, tailWord_6506026, baseEnd_6506026] using wordTrace_append hprefix tailTrace_6506026
  have hstable : (prefixWord ++ tailWord_6506026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506026).length < 2 ^ (prefixWord ++ tailWord_6506026).sum := by decide
  have hdescent : baseEnd_6506026 < baseStart_6506026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506113 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_6506113 : Nat := 118140960795 + 6506113 * 2 ^ 59
def prefixEnd_6506113 : Nat := 4983230072969 + 3 ^ 40 * 6506113 * 2
def baseEnd_6506113 : Nat := 3340763161465608536666437

theorem tailTrace_6506113 : CollatzResearch.WordTrace tailWord_6506113 prefixEnd_6506113 3340763161465608536666437 := by
  unfold tailWord_6506113
  simp only [CollatzResearch.WordTrace]
  refine ⟨237297435878471231481890993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158198290585647487654593995 237297435878471231481890993)
  ·
    refine ⟨177973076908853423611418245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237297435878471231481890993 177973076908853423611418245)
    ·
      refine ⟨33369951920410016927140921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177973076908853423611418245 33369951920410016927140921)
      ·
        refine ⟨25027463940307512695355691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33369951920410016927140921 25027463940307512695355691)
        ·
          refine ⟨37541195910461269043033537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027463940307512695355691 37541195910461269043033537)
          ·
            refine ⟨28155896932845951782275153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37541195910461269043033537 28155896932845951782275153)
            ·
              refine ⟨21116922699634463836706365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28155896932845951782275153 21116922699634463836706365)
              ·
                refine ⟨7918846012362923938764887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21116922699634463836706365 7918846012362923938764887)
                ·
                  refine ⟨11878269018544385908147331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918846012362923938764887 11878269018544385908147331)
                  ·
                    refine ⟨17817403527816578862220997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11878269018544385908147331 17817403527816578862220997)
                    ·
                      refine ⟨3340763161465608536666437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17817403527816578862220997 3340763161465608536666437)
                      ·
                        rfl

theorem cell23_6506113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_6506113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506113 prefixEnd_6506113 := by exact prefixLift 6506113
  have htrace : WordTrace (prefixWord ++ tailWord_6506113) baseStart_6506113 baseEnd_6506113 := by
    simpa [prefixWord, tailWord_6506113, baseEnd_6506113] using wordTrace_append hprefix tailTrace_6506113
  have hstable : (prefixWord ++ tailWord_6506113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506113).length < 2 ^ (prefixWord ++ tailWord_6506113).sum := by decide
  have hdescent : baseEnd_6506113 < baseStart_6506113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506119 : List Nat := [1, 1, 4, 2, 1, 3, 11]
def baseStart_6506119 : Nat := 118140960795 + 6506119 * 2 ^ 59
def prefixEnd_6506119 : Nat := 4983230072969 + 3 ^ 40 * 6506119 * 2
def baseEnd_6506119 : Nat := 41244027683327598928289

theorem tailTrace_6506119 : CollatzResearch.WordTrace tailWord_6506119 prefixEnd_6506119 41244027683327598928289 := by
  unfold tailWord_6506119
  simp only [CollatzResearch.WordTrace]
  refine ⟨237297654716449494506609411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158198436477632996337739607 237297654716449494506609411)
  ·
    refine ⟨355946482074674241759914117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237297654716449494506609411 355946482074674241759914117)
    ·
      refine ⟨66739965389001420329983897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355946482074674241759914117 66739965389001420329983897)
      ·
        refine ⟨50054974041751065247487923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66739965389001420329983897 50054974041751065247487923)
        ·
          refine ⟨75082461062626597871231885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50054974041751065247487923 75082461062626597871231885)
          ·
            refine ⟨28155922898484974201711957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75082461062626597871231885 28155922898484974201711957)
            ·
              refine ⟨41244027683327598928289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28155922898484974201711957 41244027683327598928289)
              ·
                rfl

theorem cell23_6506119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 11].length) (baseStart_6506119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506119 prefixEnd_6506119 := by exact prefixLift 6506119
  have htrace : WordTrace (prefixWord ++ tailWord_6506119) baseStart_6506119 baseEnd_6506119 := by
    simpa [prefixWord, tailWord_6506119, baseEnd_6506119] using wordTrace_append hprefix tailTrace_6506119
  have hstable : (prefixWord ++ tailWord_6506119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506119).length < 2 ^ (prefixWord ++ tailWord_6506119).sum := by decide
  have hdescent : baseEnd_6506119 < baseStart_6506119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506126 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_6506126 : Nat := 118140960795 + 6506126 * 2 ^ 59
def prefixEnd_6506126 : Nat := 4983230072969 + 3 ^ 40 * 6506126 * 2
def baseEnd_6506126 : Nat := 3340769836714116985803877

theorem tailTrace_6506126 : CollatzResearch.WordTrace tailWord_6506126 prefixEnd_6506126 3340769836714116985803877 := by
  unfold tailWord_6506126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29662238753428016837764279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158198606684949423134742821 29662238753428016837764279)
  ·
    refine ⟨44493358130142025256646419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29662238753428016837764279 44493358130142025256646419)
    ·
      refine ⟨66740037195213037884969629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44493358130142025256646419 66740037195213037884969629)
      ·
        refine ⟨25027513948204889206863611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66740037195213037884969629 25027513948204889206863611)
        ·
          refine ⟨37541270922307333810295417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027513948204889206863611 37541270922307333810295417)
          ·
            refine ⟨28155953191730500357721563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37541270922307333810295417 28155953191730500357721563)
            ·
              refine ⟨42233929787595750536582345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28155953191730500357721563 42233929787595750536582345)
              ·
                refine ⟨31675447340696812902436759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42233929787595750536582345 31675447340696812902436759)
                ·
                  refine ⟨47513171011045219353655139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31675447340696812902436759 47513171011045219353655139)
                  ·
                    refine ⟨71269756516567829030482709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47513171011045219353655139 71269756516567829030482709)
                    ·
                      refine ⟨3340769836714116985803877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71269756516567829030482709 3340769836714116985803877)
                      ·
                        rfl

theorem cell23_6506126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_6506126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506126 prefixEnd_6506126 := by exact prefixLift 6506126
  have htrace : WordTrace (prefixWord ++ tailWord_6506126) baseStart_6506126 baseEnd_6506126 := by
    simpa [prefixWord, tailWord_6506126, baseEnd_6506126] using wordTrace_append hprefix tailTrace_6506126
  have hstable : (prefixWord ++ tailWord_6506126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506126).length < 2 ^ (prefixWord ++ tailWord_6506126).sum := by decide
  have hdescent : baseEnd_6506126 < baseStart_6506126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506136 : List Nat := [2, 1, 2, 4, 1, 3, 2, 8]
def baseStart_6506136 : Nat := 118140960795 + 6506136 * 2 ^ 59
def prefixEnd_6506136 : Nat := 4983230072969 + 3 ^ 40 * 6506136 * 2
def baseEnd_6506136 : Nat := 123732406352617109136253

theorem tailTrace_6506136 : CollatzResearch.WordTrace tailWord_6506136 prefixEnd_6506136 123732406352617109136253 := by
  unfold tailWord_6506136
  simp only [CollatzResearch.WordTrace]
  refine ⟨118649137378693953204989131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158198849838258604273318841 118649137378693953204989131)
  ·
    refine ⟨177973706068040929807483697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118649137378693953204989131 177973706068040929807483697)
    ·
      refine ⟨133480279551030697355612773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177973706068040929807483697 133480279551030697355612773)
      ·
        refine ⟨25027552415818255754177395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133480279551030697355612773 25027552415818255754177395)
        ·
          refine ⟨37541328623727383631266093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027552415818255754177395 37541328623727383631266093)
          ·
            refine ⟨14077998233897768861724785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37541328623727383631266093 14077998233897768861724785)
            ·
              refine ⟨10558498675423326646293589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14077998233897768861724785 10558498675423326646293589)
              ·
                refine ⟨123732406352617109136253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10558498675423326646293589 123732406352617109136253)
                ·
                  rfl

theorem cell23_6506136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 8].length) (baseStart_6506136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506136 prefixEnd_6506136 := by exact prefixLift 6506136
  have htrace : WordTrace (prefixWord ++ tailWord_6506136) baseStart_6506136 baseEnd_6506136 := by
    simpa [prefixWord, tailWord_6506136, baseEnd_6506136] using wordTrace_append hprefix tailTrace_6506136
  have hstable : (prefixWord ++ tailWord_6506136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506136).length < 2 ^ (prefixWord ++ tailWord_6506136).sum := by decide
  have hdescent : baseEnd_6506136 < baseStart_6506136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506140 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_6506140 : Nat := 118140960795 + 6506140 * 2 ^ 59
def prefixEnd_6506140 : Nat := 4983230072969 + 3 ^ 40 * 6506140 * 2
def baseEnd_6506140 : Nat := 1113592341814426643676271

theorem tailTrace_6506140 : CollatzResearch.WordTrace tailWord_6506140 prefixEnd_6506140 1113592341814426643676271 := by
  unfold tailWord_6506140
  simp only [CollatzResearch.WordTrace]
  refine ⟨118649210324686707546561937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158198947099582276728749249 118649210324686707546561937)
  ·
    refine ⟨88986907743515030659921453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118649210324686707546561937 88986907743515030659921453)
    ·
      refine ⟨33370090403818136497470545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88986907743515030659921453 33370090403818136497470545)
      ·
        refine ⟨25027567802863602373102909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33370090403818136497470545 25027567802863602373102909)
        ·
          refine ⟨9385337926073850889913591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25027567802863602373102909 9385337926073850889913591)
          ·
            refine ⟨14078006889110776334870387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9385337926073850889913591 14078006889110776334870387)
            ·
              refine ⟨21117010333666164502305581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14078006889110776334870387 21117010333666164502305581)
              ·
                refine ⟨7918878875124811688364593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21117010333666164502305581 7918878875124811688364593)
                ·
                  refine ⟨5939159156343608766273445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7918878875124811688364593 5939159156343608766273445)
                  ·
                    refine ⟨1113592341814426643676271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5939159156343608766273445 1113592341814426643676271)
                    ·
                      rfl

theorem cell23_6506140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_6506140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506140 prefixEnd_6506140 := by exact prefixLift 6506140
  have htrace : WordTrace (prefixWord ++ tailWord_6506140) baseStart_6506140 baseEnd_6506140 := by
    simpa [prefixWord, tailWord_6506140, baseEnd_6506140] using wordTrace_append hprefix tailTrace_6506140
  have hstable : (prefixWord ++ tailWord_6506140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506140).length < 2 ^ (prefixWord ++ tailWord_6506140).sum := by decide
  have hdescent : baseEnd_6506140 < baseStart_6506140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506179 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 8]
def baseStart_6506179 : Nat := 118140960795 + 6506179 * 2 ^ 59
def prefixEnd_6506179 : Nat := 4983230072969 + 3 ^ 40 * 6506179 * 2
def baseEnd_6506179 : Nat := 1113599017062935092813711

theorem tailTrace_6506179 : CollatzResearch.WordTrace tailWord_6506179 prefixEnd_6506179 1113599017062935092813711 := by
  unfold tailWord_6506179
  simp only [CollatzResearch.WordTrace]
  refine ⟨237299843096232124753793591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158199895397488083169195727 237299843096232124753793591)
  ·
    refine ⟨355949764644348187130690387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237299843096232124753793591 355949764644348187130690387)
    ·
      refine ⟨533924646966522280696035581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355949764644348187130690387 533924646966522280696035581)
      ·
        refine ⟨200221742612445855261013343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533924646966522280696035581 200221742612445855261013343)
        ·
          refine ⟨300332613918668782891520015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200221742612445855261013343 300332613918668782891520015)
          ·
            refine ⟨450498920878003174337280023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300332613918668782891520015 450498920878003174337280023)
            ·
              refine ⟨675748381317004761505920035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450498920878003174337280023 675748381317004761505920035)
              ·
                refine ⟨1013622571975507142258880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675748381317004761505920035 1013622571975507142258880053)
                ·
                  refine ⟨95027116122703794586770005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1013622571975507142258880053 95027116122703794586770005)
                  ·
                    refine ⟨1113599017062935092813711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95027116122703794586770005 1113599017062935092813711)
                    ·
                      rfl

theorem cell23_6506179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_6506179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506179 prefixEnd_6506179 := by exact prefixLift 6506179
  have htrace : WordTrace (prefixWord ++ tailWord_6506179) baseStart_6506179 baseEnd_6506179 := by
    simpa [prefixWord, tailWord_6506179, baseEnd_6506179] using wordTrace_append hprefix tailTrace_6506179
  have hstable : (prefixWord ++ tailWord_6506179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506179).length < 2 ^ (prefixWord ++ tailWord_6506179).sum := by decide
  have hdescent : baseEnd_6506179 < baseStart_6506179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506226 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_6506226 : Nat := 118140960795 + 6506226 * 2 ^ 59
def prefixEnd_6506226 : Nat := 4983230072969 + 3 ^ 40 * 6506226 * 2
def baseEnd_6506226 : Nat := 371202353864396288283713

theorem tailTrace_6506226 : CollatzResearch.WordTrace tailWord_6506226 prefixEnd_6506226 371202353864396288283713 := by
  unfold tailWord_6506226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59325389331765462945188633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158201038218041234520503021 59325389331765462945188633)
  ·
    refine ⟨44494041998824097208891475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59325389331765462945188633 44494041998824097208891475)
    ·
      refine ⟨66741062998236145813337213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44494041998824097208891475 66741062998236145813337213)
      ·
        refine ⟨25027898624338554680001455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66741062998236145813337213 25027898624338554680001455)
        ·
          refine ⟨37541847936507832020002183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027898624338554680001455 37541847936507832020002183)
          ·
            refine ⟨56312771904761748030003275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37541847936507832020002183 56312771904761748030003275)
            ·
              refine ⟨84469157857142622045004913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56312771904761748030003275 84469157857142622045004913)
              ·
                refine ⟨63351868392856966533753685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84469157857142622045004913 63351868392856966533753685)
                ·
                  refine ⟨371202353864396288283713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63351868392856966533753685 371202353864396288283713)
                  ·
                    rfl

theorem cell23_6506226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_6506226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506226 prefixEnd_6506226 := by exact prefixLift 6506226
  have htrace : WordTrace (prefixWord ++ tailWord_6506226) baseStart_6506226 baseEnd_6506226 := by
    simpa [prefixWord, tailWord_6506226, baseEnd_6506226] using wordTrace_append hprefix tailTrace_6506226
  have hstable : (prefixWord ++ tailWord_6506226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506226).length < 2 ^ (prefixWord ++ tailWord_6506226).sum := by decide
  have hdescent : baseEnd_6506226 < baseStart_6506226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506243 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 5]
def baseStart_6506243 : Nat := 118140960795 + 6506243 * 2 ^ 59
def prefixEnd_6506243 : Nat := 4983230072969 + 3 ^ 40 * 6506243 * 2
def baseEnd_6506243 : Nat := 371203323772299225337871

theorem tailTrace_6506243 : CollatzResearch.WordTrace tailWord_6506243 prefixEnd_6506243 371203323772299225337871 := by
  unfold tailWord_6506243
  simp only [CollatzResearch.WordTrace]
  refine ⟨237302177368000263684123383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158201451578666842456082255 237302177368000263684123383)
  ·
    refine ⟨355953266052000395526185075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237302177368000263684123383 355953266052000395526185075)
    ·
      refine ⟨533929899078000593289277613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355953266052000395526185075 533929899078000593289277613)
      ·
        refine ⟨200223712154250222483479105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533929899078000593289277613 200223712154250222483479105)
        ·
          refine ⟨150167784115687666862609329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200223712154250222483479105 150167784115687666862609329)
          ·
            refine ⟨112625838086765750146956997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150167784115687666862609329 112625838086765750146956997)
            ·
              refine ⟨21117344641268578152554437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112625838086765750146956997 21117344641268578152554437)
              ·
                refine ⟨3959502120237858403603957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21117344641268578152554437 3959502120237858403603957)
                ·
                  refine ⟨371203323772299225337871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3959502120237858403603957 371203323772299225337871)
                  ·
                    rfl

theorem cell23_6506243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 5].length) (baseStart_6506243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506243 prefixEnd_6506243 := by exact prefixLift 6506243
  have htrace : WordTrace (prefixWord ++ tailWord_6506243) baseStart_6506243 baseEnd_6506243 := by
    simpa [prefixWord, tailWord_6506243, baseEnd_6506243] using wordTrace_append hprefix tailTrace_6506243
  have hstable : (prefixWord ++ tailWord_6506243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506243).length < 2 ^ (prefixWord ++ tailWord_6506243).sum := by decide
  have hdescent : baseEnd_6506243 < baseStart_6506243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506294 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_6506294 : Nat := 118140960795 + 6506294 * 2 ^ 59
def prefixEnd_6506294 : Nat := 4983230072969 + 3 ^ 40 * 6506294 * 2
def baseEnd_6506294 : Nat := 371206233496008036500345

theorem tailTrace_6506294 : CollatzResearch.WordTrace tailWord_6506294 prefixEnd_6506294 371206233496008036500345 := by
  unfold tailWord_6506294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831502343175968712139371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158202691660543666262819957 14831502343175968712139371)
  ·
    refine ⟨22247253514763953068209057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14831502343175968712139371 22247253514763953068209057)
    ·
      refine ⟨16685440136072964801156793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22247253514763953068209057 16685440136072964801156793)
      ·
        refine ⟨12514080102054723600867595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16685440136072964801156793 12514080102054723600867595)
        ·
          refine ⟨18771120153082085401301393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12514080102054723600867595 18771120153082085401301393)
          ·
            refine ⟨14078340114811564050976045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18771120153082085401301393 14078340114811564050976045)
            ·
              refine ⟨5279377543054336519116017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14078340114811564050976045 5279377543054336519116017)
              ·
                refine ⟨3959533157290752389337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5279377543054336519116017 3959533157290752389337013)
                ·
                  refine ⟨371206233496008036500345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3959533157290752389337013 371206233496008036500345)
                  ·
                    rfl

theorem cell23_6506294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_6506294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506294 prefixEnd_6506294 := by exact prefixLift 6506294
  have htrace : WordTrace (prefixWord ++ tailWord_6506294) baseStart_6506294 baseEnd_6506294 := by
    simpa [prefixWord, tailWord_6506294, baseEnd_6506294] using wordTrace_append hprefix tailTrace_6506294
  have hstable : (prefixWord ++ tailWord_6506294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506294).length < 2 ^ (prefixWord ++ tailWord_6506294).sum := by decide
  have hdescent : baseEnd_6506294 < baseStart_6506294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506313 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_6506313 : Nat := 118140960795 + 6506313 * 2 ^ 59
def prefixEnd_6506313 : Nat := 4983230072969 + 3 ^ 40 * 6506313 * 2
def baseEnd_6506313 : Nat := 3340865857596507754165517

theorem tailTrace_6506313 : CollatzResearch.WordTrace tailWord_6506313 prefixEnd_6506313 3340865857596507754165517 := by
  unfold tailWord_6506313
  simp only [CollatzResearch.WordTrace]
  refine ⟨237304730477746665639171593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158203153651831110426114395 237304730477746665639171593)
  ·
    refine ⟨177978547858309999229378695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237304730477746665639171593 177978547858309999229378695)
    ·
      refine ⟨266967821787464998844068043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177978547858309999229378695 266967821787464998844068043)
      ·
        refine ⟨400451732681197498266102065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266967821787464998844068043 400451732681197498266102065)
        ·
          refine ⟨300338799510898123699576549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400451732681197498266102065 300338799510898123699576549)
          ·
            refine ⟨56313524908293398193670603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300338799510898123699576549 56313524908293398193670603)
            ·
              refine ⟨84470287362440097290505905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56313524908293398193670603 84470287362440097290505905)
              ·
                refine ⟨63352715521830072967879429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84470287362440097290505905 63352715521830072967879429)
                ·
                  refine ⟨11878634160343138681477393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63352715521830072967879429 11878634160343138681477393)
                  ·
                    refine ⟨8908975620257354011108045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11878634160343138681477393 8908975620257354011108045)
                    ·
                      refine ⟨3340865857596507754165517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908975620257354011108045 3340865857596507754165517)
                      ·
                        rfl

theorem cell23_6506313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_6506313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506313 prefixEnd_6506313 := by exact prefixLift 6506313
  have htrace : WordTrace (prefixWord ++ tailWord_6506313) baseStart_6506313 baseEnd_6506313 := by
    simpa [prefixWord, tailWord_6506313, baseEnd_6506313] using wordTrace_append hprefix tailTrace_6506313
  have hstable : (prefixWord ++ tailWord_6506313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506313).length < 2 ^ (prefixWord ++ tailWord_6506313).sum := by decide
  have hdescent : baseEnd_6506313 < baseStart_6506313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506330 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_6506330 : Nat := 118140960795 + 6506330 * 2 ^ 59
def prefixEnd_6506330 : Nat := 4983230072969 + 3 ^ 40 * 6506330 * 2
def baseEnd_6506330 : Nat := 3340874586767634187652939

theorem tailTrace_6506330 : CollatzResearch.WordTrace tailWord_6506330 prefixEnd_6506330 3340874586767634187652939 := by
  unfold tailWord_6506330
  simp only [CollatzResearch.WordTrace]
  refine ⟨59326337629671269385635111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158203567012456718361693629 59326337629671269385635111)
  ·
    refine ⟨88989506444506904078452667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59326337629671269385635111 88989506444506904078452667)
    ·
      refine ⟨133484259666760356117679001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88989506444506904078452667 133484259666760356117679001)
      ·
        refine ⟨100113194750070267088259251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133484259666760356117679001 100113194750070267088259251)
        ·
          refine ⟨150169792125105400632388877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100113194750070267088259251 150169792125105400632388877)
          ·
            refine ⟨56313672046914525237145829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150169792125105400632388877 56313672046914525237145829)
            ·
              refine ⟨10558813508796473481964843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56313672046914525237145829 10558813508796473481964843)
              ·
                refine ⟨15838220263194710222947265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10558813508796473481964843 15838220263194710222947265)
                ·
                  refine ⟨11878665197396032667210449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15838220263194710222947265 11878665197396032667210449)
                  ·
                    refine ⟨8908998898047024500407837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11878665197396032667210449 8908998898047024500407837)
                    ·
                      refine ⟨3340874586767634187652939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8908998898047024500407837 3340874586767634187652939)
                      ·
                        rfl

theorem cell23_6506330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_6506330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506330 prefixEnd_6506330 := by exact prefixLift 6506330
  have htrace : WordTrace (prefixWord ++ tailWord_6506330) baseStart_6506330 baseEnd_6506330 := by
    simpa [prefixWord, tailWord_6506330, baseEnd_6506330] using wordTrace_append hprefix tailTrace_6506330
  have hstable : (prefixWord ++ tailWord_6506330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506330).length < 2 ^ (prefixWord ++ tailWord_6506330).sum := by decide
  have hdescent : baseEnd_6506330 < baseStart_6506330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506350 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_6506350 : Nat := 118140960795 + 6506350 * 2 ^ 59
def prefixEnd_6506350 : Nat := 4983230072969 + 3 ^ 40 * 6506350 * 2
def baseEnd_6506350 : Nat := 371209428486747123266983

theorem tailTrace_6506350 : CollatzResearch.WordTrace tailWord_6506350 prefixEnd_6506350 371209428486747123266983 := by
  unfold tailWord_6506350
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663259997326577619783563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158204053319075080638845669 29663259997326577619783563)
  ·
    refine ⟨44494889995989866429675345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29663259997326577619783563 44494889995989866429675345)
    ·
      refine ⟨33371167496992399822256509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44494889995989866429675345 33371167496992399822256509)
      ·
        refine ⟨12514187811372149933346191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33371167496992399822256509 12514187811372149933346191)
        ·
          refine ⟨18771281717058224900019287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12514187811372149933346191 18771281717058224900019287)
          ·
            refine ⟨28156922575587337350028931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18771281717058224900019287 28156922575587337350028931)
            ·
              refine ⟨42235383863381006025043397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28156922575587337350028931 42235383863381006025043397)
              ·
                refine ⟨7919134474383938629695637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42235383863381006025043397 7919134474383938629695637)
                ·
                  refine ⟨371209428486747123266983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7919134474383938629695637 371209428486747123266983)
                  ·
                    rfl

theorem cell23_6506350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_6506350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506350 prefixEnd_6506350 := by exact prefixLift 6506350
  have htrace : WordTrace (prefixWord ++ tailWord_6506350) baseStart_6506350 baseEnd_6506350 := by
    simpa [prefixWord, tailWord_6506350, baseEnd_6506350] using wordTrace_append hprefix tailTrace_6506350
  have hstable : (prefixWord ++ tailWord_6506350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506350).length < 2 ^ (prefixWord ++ tailWord_6506350).sum := by decide
  have hdescent : baseEnd_6506350 < baseStart_6506350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506393 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_6506393 : Nat := 118140960795 + 6506393 * 2 ^ 59
def prefixEnd_6506393 : Nat := 4983230072969 + 3 ^ 40 * 6506393 * 2
def baseEnd_6506393 : Nat := 1113635645349622480388383

theorem tailTrace_6506393 : CollatzResearch.WordTrace tailWord_6506393 prefixEnd_6506393 1113635645349622480388383 := by
  unfold tailWord_6506393
  simp only [CollatzResearch.WordTrace]
  refine ⟨237307648317456839302083833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158205098878304559534722555 237307648317456839302083833)
  ·
    refine ⟨177980736238092629476562875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237307648317456839302083833 177980736238092629476562875)
    ·
      refine ⟨266971104357138944214844313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177980736238092629476562875 266971104357138944214844313)
      ·
        refine ⟨200228328267854208161133235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266971104357138944214844313 200228328267854208161133235)
        ·
          refine ⟨300342492401781312241699853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200228328267854208161133235 300342492401781312241699853)
          ·
            refine ⟨112628434650667992090637445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300342492401781312241699853 112628434650667992090637445)
            ·
              refine ⟨21117831497000248516994521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112628434650667992090637445 21117831497000248516994521)
              ·
                refine ⟨15838373622750186387745891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21117831497000248516994521 15838373622750186387745891)
                ·
                  refine ⟨23757560434125279581618837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15838373622750186387745891 23757560434125279581618837)
                  ·
                    refine ⟨1113635645349622480388383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23757560434125279581618837 1113635645349622480388383)
                    ·
                      rfl

theorem cell23_6506393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_6506393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506393 prefixEnd_6506393 := by exact prefixLift 6506393
  have htrace : WordTrace (prefixWord ++ tailWord_6506393) baseStart_6506393 baseEnd_6506393 := by
    simpa [prefixWord, tailWord_6506393, baseEnd_6506393] using wordTrace_append hprefix tailTrace_6506393
  have hstable : (prefixWord ++ tailWord_6506393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506393).length < 2 ^ (prefixWord ++ tailWord_6506393).sum := by decide
  have hdescent : baseEnd_6506393 < baseStart_6506393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506394 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6506394 : Nat := 118140960795 + 6506394 * 2 ^ 59
def prefixEnd_6506394 : Nat := 4983230072969 + 3 ^ 40 * 6506394 * 2
def baseEnd_6506394 : Nat := 3340907449529521937252645

theorem tailTrace_6506394 : CollatzResearch.WordTrace tailWord_6506394 prefixEnd_6506394 3340907449529521937252645 := by
  unfold tailWord_6506394
  simp only [CollatzResearch.WordTrace]
  refine ⟨59326921197613304118217559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158205123193635477648580157 59326921197613304118217559)
  ·
    refine ⟨88990381796419956177326339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59326921197613304118217559 88990381796419956177326339)
    ·
      refine ⟨133485572694629934265989509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88990381796419956177326339 133485572694629934265989509)
      ·
        refine ⟨25028544880243112674873033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133485572694629934265989509 25028544880243112674873033)
        ·
          refine ⟨18771408660182334506154775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25028544880243112674873033 18771408660182334506154775)
          ·
            refine ⟨28157112990273501759232163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18771408660182334506154775 28157112990273501759232163)
            ·
              refine ⟨42235669485410252638848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28157112990273501759232163 42235669485410252638848245)
              ·
                refine ⟨3959594014257211184892023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42235669485410252638848245 3959594014257211184892023)
                ·
                  refine ⟨5939391021385816777338035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959594014257211184892023 5939391021385816777338035)
                  ·
                    refine ⟨8909086532078725166007053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5939391021385816777338035 8909086532078725166007053)
                    ·
                      refine ⟨3340907449529521937252645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909086532078725166007053 3340907449529521937252645)
                      ·
                        rfl

theorem cell23_6506394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6506394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506394 prefixEnd_6506394 := by exact prefixLift 6506394
  have htrace : WordTrace (prefixWord ++ tailWord_6506394) baseStart_6506394 baseEnd_6506394 := by
    simpa [prefixWord, tailWord_6506394, baseEnd_6506394] using wordTrace_append hprefix tailTrace_6506394
  have hstable : (prefixWord ++ tailWord_6506394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506394).length < 2 ^ (prefixWord ++ tailWord_6506394).sum := by decide
  have hdescent : baseEnd_6506394 < baseStart_6506394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506397 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6506397 : Nat := 118140960795 + 6506397 * 2 ^ 59
def prefixEnd_6506397 : Nat := 4983230072969 + 3 ^ 40 * 6506397 * 2
def baseEnd_6506397 : Nat := 1113636329990495141838377

theorem tailTrace_6506397 : CollatzResearch.WordTrace tailWord_6506397 prefixEnd_6506397 1113636329990495141838377 := by
  unfold tailWord_6506397
  simp only [CollatzResearch.WordTrace]
  refine ⟨237307794209442347985229445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158205196139628231990152963 237307794209442347985229445)
  ·
    refine ⟨44495211414270440247230521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237307794209442347985229445 44495211414270440247230521)
    ·
      refine ⟨33371408560702830185422891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44495211414270440247230521 33371408560702830185422891)
      ·
        refine ⟨50057112841054245278134337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33371408560702830185422891 50057112841054245278134337)
        ·
          refine ⟨37542834630790683958600753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50057112841054245278134337 37542834630790683958600753)
          ·
            refine ⟨28157125973093012968950565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37542834630790683958600753 28157125973093012968950565)
            ·
              refine ⟨5279461119954939931678231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28157125973093012968950565 5279461119954939931678231)
              ·
                refine ⟨7919191679932409897517347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279461119954939931678231 7919191679932409897517347)
                ·
                  refine ⟨11878787519898614846276021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7919191679932409897517347 11878787519898614846276021)
                  ·
                    refine ⟨1113636329990495141838377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11878787519898614846276021 1113636329990495141838377)
                    ·
                      rfl

theorem cell23_6506397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6506397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506397 prefixEnd_6506397 := by exact prefixLift 6506397
  have htrace : WordTrace (prefixWord ++ tailWord_6506397) baseStart_6506397 baseEnd_6506397 := by
    simpa [prefixWord, tailWord_6506397, baseEnd_6506397] using wordTrace_append hprefix tailTrace_6506397
  have hstable : (prefixWord ++ tailWord_6506397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506397).length < 2 ^ (prefixWord ++ tailWord_6506397).sum := by decide
  have hdescent : baseEnd_6506397 < baseStart_6506397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506403 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5]
def baseStart_6506403 : Nat := 118140960795 + 6506403 * 2 ^ 59
def prefixEnd_6506403 : Nat := 4983230072969 + 3 ^ 40 * 6506403 * 2
def baseEnd_6506403 : Nat := 3340912070855412402040103

theorem tailTrace_6506403 : CollatzResearch.WordTrace tailWord_6506403 prefixEnd_6506403 3340912070855412402040103 := by
  unfold tailWord_6506403
  simp only [CollatzResearch.WordTrace]
  refine ⟨237308013047420611009947863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158205342031613740673298575 237308013047420611009947863)
  ·
    refine ⟨355962019571130916514921795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237308013047420611009947863 355962019571130916514921795)
    ·
      refine ⟨533943029356696374772382693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355962019571130916514921795 533943029356696374772382693)
      ·
        refine ⟨100114318004380570269821755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 533943029356696374772382693 100114318004380570269821755)
        ·
          refine ⟨150171477006570855404732633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100114318004380570269821755 150171477006570855404732633)
          ·
            refine ⟨112628607754928141553549475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150171477006570855404732633 112628607754928141553549475)
            ·
              refine ⟨168942911632392212330324213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112628607754928141553549475 168942911632392212330324213)
              ·
                refine ⟨15838397965536769905967895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168942911632392212330324213 15838397965536769905967895)
                ·
                  refine ⟨23757596948305154858951843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15838397965536769905967895 23757596948305154858951843)
                  ·
                    refine ⟨35636395422457732288427765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23757596948305154858951843 35636395422457732288427765)
                    ·
                      refine ⟨3340912070855412402040103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35636395422457732288427765 3340912070855412402040103)
                      ·
                        rfl

theorem cell23_6506403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_6506403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506403 prefixEnd_6506403 := by exact prefixLift 6506403
  have htrace : WordTrace (prefixWord ++ tailWord_6506403) baseStart_6506403 baseEnd_6506403 := by
    simpa [prefixWord, tailWord_6506403, baseEnd_6506403] using wordTrace_append hprefix tailTrace_6506403
  have hstable : (prefixWord ++ tailWord_6506403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506403).length < 2 ^ (prefixWord ++ tailWord_6506403).sum := by decide
  have hdescent : baseEnd_6506403 < baseStart_6506403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506430 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_6506430 : Nat := 118140960795 + 6506430 * 2 ^ 59
def prefixEnd_6506430 : Nat := 4983230072969 + 3 ^ 40 * 6506430 * 2
def baseEnd_6506430 : Nat := 3340925934833083796402479

theorem tailTrace_6506430 : CollatzResearch.WordTrace tailWord_6506430 prefixEnd_6506430 3340925934833083796402479 := by
  unfold tailWord_6506430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663624727290349327647593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158205998545548529747453829 29663624727290349327647593)
  ·
    refine ⟨22247718545467761995735695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29663624727290349327647593 22247718545467761995735695)
    ·
      refine ⟨33371577818201642993603543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22247718545467761995735695 33371577818201642993603543)
      ·
        refine ⟨50057366727302464490405315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33371577818201642993603543 50057366727302464490405315)
        ·
          refine ⟨75086050090953696735607973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50057366727302464490405315 75086050090953696735607973)
          ·
            refine ⟨14078634392053818137926495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75086050090953696735607973 14078634392053818137926495)
            ·
              refine ⟨21117951588080727206889743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14078634392053818137926495 21117951588080727206889743)
              ·
                refine ⟨31676927382121090810334615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21117951588080727206889743 31676927382121090810334615)
                ·
                  refine ⟨47515391073181636215501923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31676927382121090810334615 47515391073181636215501923)
                  ·
                    refine ⟨71273086609772454323252885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47515391073181636215501923 71273086609772454323252885)
                    ·
                      refine ⟨3340925934833083796402479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71273086609772454323252885 3340925934833083796402479)
                      ·
                        rfl

theorem cell23_6506430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_6506430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506430 prefixEnd_6506430 := by exact prefixLift 6506430
  have htrace : WordTrace (prefixWord ++ tailWord_6506430) baseStart_6506430 baseEnd_6506430 := by
    simpa [prefixWord, tailWord_6506430, baseEnd_6506430] using wordTrace_append hprefix tailTrace_6506430
  have hstable : (prefixWord ++ tailWord_6506430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506430).length < 2 ^ (prefixWord ++ tailWord_6506430).sum := by decide
  have hdescent : baseEnd_6506430 < baseStart_6506430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506440 : List Nat := [2, 1, 3, 1, 4, 1, 4, 7]
def baseStart_6506440 : Nat := 118140960795 + 6506440 * 2 ^ 59
def prefixEnd_6506440 : Nat := 4983230072969 + 3 ^ 40 * 6506440 * 2
def baseEnd_6506440 : Nat := 123738187764430694713979

theorem tailTrace_6506440 : CollatzResearch.WordTrace tailWord_6506440 prefixEnd_6506440 123738187764430694713979 := by
  unfold tailWord_6506440
  simp only [CollatzResearch.WordTrace]
  refine ⟨118654681274143283164522387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158206241698857710886029849 118654681274143283164522387)
  ·
    refine ⟨177982021911214924746783581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118654681274143283164522387 177982021911214924746783581)
    ·
      refine ⟨66743258216705596780043843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177982021911214924746783581 66743258216705596780043843)
      ·
        refine ⟨100114887325058395170065765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66743258216705596780043843 100114887325058395170065765)
        ·
          refine ⟨18771541373448449094387331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100114887325058395170065765 18771541373448449094387331)
          ·
            refine ⟨28157312060172673641580997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18771541373448449094387331 28157312060172673641580997)
            ·
              refine ⟨5279496011282376307796437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28157312060172673641580997 5279496011282376307796437)
              ·
                refine ⟨123738187764430694713979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5279496011282376307796437 123738187764430694713979)
                ·
                  rfl

theorem cell23_6506440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 7].length) (baseStart_6506440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506440 prefixEnd_6506440 := by exact prefixLift 6506440
  have htrace : WordTrace (prefixWord ++ tailWord_6506440) baseStart_6506440 baseEnd_6506440 := by
    simpa [prefixWord, tailWord_6506440, baseEnd_6506440] using wordTrace_append hprefix tailTrace_6506440
  have hstable : (prefixWord ++ tailWord_6506440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506440).length < 2 ^ (prefixWord ++ tailWord_6506440).sum := by decide
  have hdescent : baseEnd_6506440 < baseStart_6506440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506454 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6506454 : Nat := 118140960795 + 6506454 * 2 ^ 59
def prefixEnd_6506454 : Nat := 4983230072969 + 3 ^ 40 * 6506454 * 2
def baseEnd_6506454 : Nat := 3340938258368791702502369

theorem tailTrace_6506454 : CollatzResearch.WordTrace tailWord_6506454 prefixEnd_6506454 3340938258368791702502369 := by
  unfold tailWord_6506454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831867073139740420003401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158206582113490564480036277 14831867073139740420003401)
  ·
    refine ⟨11123900304854805315002551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14831867073139740420003401 11123900304854805315002551)
    ·
      refine ⟨16685850457282207972503827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123900304854805315002551 16685850457282207972503827)
      ·
        refine ⟨25028775685923311958755741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16685850457282207972503827 25028775685923311958755741)
        ·
          refine ⟨9385790882221241984533403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25028775685923311958755741 9385790882221241984533403)
          ·
            refine ⟨14078686323331862976800105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9385790882221241984533403 14078686323331862976800105)
            ·
              refine ⟨10559014742498897232600079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14078686323331862976800105 10559014742498897232600079)
              ·
                refine ⟨15838522113748345848900119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10559014742498897232600079 15838522113748345848900119)
                ·
                  refine ⟨23757783170622518773350179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15838522113748345848900119 23757783170622518773350179)
                  ·
                    refine ⟨35636674755933778160025269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23757783170622518773350179 35636674755933778160025269)
                    ·
                      refine ⟨3340938258368791702502369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35636674755933778160025269 3340938258368791702502369)
                      ·
                        rfl

theorem cell23_6506454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6506454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506454 prefixEnd_6506454 := by exact prefixLift 6506454
  have htrace : WordTrace (prefixWord ++ tailWord_6506454) baseStart_6506454 baseEnd_6506454 := by
    simpa [prefixWord, tailWord_6506454, baseEnd_6506454] using wordTrace_append hprefix tailTrace_6506454
  have hstable : (prefixWord ++ tailWord_6506454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506454).length < 2 ^ (prefixWord ++ tailWord_6506454).sum := by decide
  have hdescent : baseEnd_6506454 < baseStart_6506454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506467 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 3]
def baseStart_6506467 : Nat := 118140960795 + 6506467 * 2 ^ 59
def prefixEnd_6506467 : Nat := 4983230072969 + 3 ^ 40 * 6506467 * 2
def baseEnd_6506467 : Nat := 3340944933617300151639809

theorem tailTrace_6506467 : CollatzResearch.WordTrace tailWord_6506467 prefixEnd_6506467 3340944933617300151639809 := by
  unfold tailWord_6506467
  simp only [CollatzResearch.WordTrace]
  refine ⟨237310347319188749940277655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158206898212792499960185103 237310347319188749940277655)
  ·
    refine ⟨355965520978783124910416483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237310347319188749940277655 355965520978783124910416483)
    ·
      refine ⟨533948281468174687365624725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355965520978783124910416483 533948281468174687365624725)
      ·
        refine ⟨25028825693820688470263659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 533948281468174687365624725 25028825693820688470263659)
        ·
          refine ⟨37543238540731032705395489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25028825693820688470263659 37543238540731032705395489)
          ·
            refine ⟨28157428905548274529046617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37543238540731032705395489 28157428905548274529046617)
            ·
              refine ⟨21118071679161205896784963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28157428905548274529046617 21118071679161205896784963)
              ·
                refine ⟨31677107518741808845177445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21118071679161205896784963 31677107518741808845177445)
                ·
                  refine ⟨5939457659764089158470771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31677107518741808845177445 5939457659764089158470771)
                  ·
                    refine ⟨8909186489646133737706157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5939457659764089158470771 8909186489646133737706157)
                    ·
                      refine ⟨3340944933617300151639809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909186489646133737706157 3340944933617300151639809)
                      ·
                        rfl

theorem cell23_6506467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_6506467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506467 prefixEnd_6506467 := by exact prefixLift 6506467
  have htrace : WordTrace (prefixWord ++ tailWord_6506467) baseStart_6506467 baseEnd_6506467 := by
    simpa [prefixWord, tailWord_6506467, baseEnd_6506467] using wordTrace_append hprefix tailTrace_6506467
  have hstable : (prefixWord ++ tailWord_6506467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506467).length < 2 ^ (prefixWord ++ tailWord_6506467).sum := by decide
  have hdescent : baseEnd_6506467 < baseStart_6506467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506483 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 2, 6]
def baseStart_6506483 : Nat := 118140960795 + 6506483 * 2 ^ 59
def prefixEnd_6506483 : Nat := 4983230072969 + 3 ^ 40 * 6506483 * 2
def baseEnd_6506483 : Nat := 1113651049769257363013245

theorem tailTrace_6506483 : CollatzResearch.WordTrace tailWord_6506483 prefixEnd_6506483 1113651049769257363013245 := by
  unfold tailWord_6506483
  simp only [CollatzResearch.WordTrace]
  refine ⟨237310930887130784672860103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158207287258087189781906735 237310930887130784672860103)
  ·
    refine ⟨355966396330696177009290155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237310930887130784672860103 355966396330696177009290155)
    ·
      refine ⟨533949594496044265513935233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355966396330696177009290155 533949594496044265513935233)
      ·
        refine ⟨400462195872033199135451425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533949594496044265513935233 400462195872033199135451425)
        ·
          refine ⟨300346646904024899351588569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400462195872033199135451425 300346646904024899351588569)
          ·
            refine ⟨225259985178018674513691427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300346646904024899351588569 225259985178018674513691427)
            ·
              refine ⟨337889977767028011770537141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225259985178018674513691427 337889977767028011770537141)
              ·
                refine ⟨31677185415658876103487857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337889977767028011770537141 31677185415658876103487857)
                ·
                  refine ⟨23757889061744157077615893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31677185415658876103487857 23757889061744157077615893)
                  ·
                    refine ⟨1113651049769257363013245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23757889061744157077615893 1113651049769257363013245)
                    ·
                      rfl

theorem cell23_6506483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_6506483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506483 prefixEnd_6506483 := by exact prefixLift 6506483
  have htrace : WordTrace (prefixWord ++ tailWord_6506483) baseStart_6506483 baseEnd_6506483 := by
    simpa [prefixWord, tailWord_6506483, baseEnd_6506483] using wordTrace_append hprefix tailTrace_6506483
  have hstable : (prefixWord ++ tailWord_6506483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506483).length < 2 ^ (prefixWord ++ tailWord_6506483).sum := by decide
  have hdescent : baseEnd_6506483 < baseStart_6506483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506507 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 1, 4, 2]
def baseStart_6506507 : Nat := 118140960795 + 6506507 * 2 ^ 59
def prefixEnd_6506507 : Nat := 4983230072969 + 3 ^ 40 * 6506507 * 2
def baseEnd_6506507 : Nat := 3340965472843479995139625

theorem tailTrace_6506507 : CollatzResearch.WordTrace tailWord_6506507 prefixEnd_6506507 3340965472843479995139625 := by
  unfold tailWord_6506507
  simp only [CollatzResearch.WordTrace]
  refine ⟨237311806239043836771733775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158207870826029224514489183 237311806239043836771733775)
  ·
    refine ⟨355967709358565755157600663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237311806239043836771733775 355967709358565755157600663)
    ·
      refine ⟨533951564037848632736400995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355967709358565755157600663 533951564037848632736400995)
      ·
        refine ⟨800927346056772949104601493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533951564037848632736400995 800927346056772949104601493)
        ·
          refine ⟨37543469346411231989278195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 800927346056772949104601493 37543469346411231989278195)
          ·
            refine ⟨56315204019616847983917293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37543469346411231989278195 56315204019616847983917293)
            ·
              refine ⟨21118201507356317993968985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56315204019616847983917293 21118201507356317993968985)
              ·
                refine ⟨15838651130517238495476739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21118201507356317993968985 15838651130517238495476739)
                ·
                  refine ⟨23757976695775857743215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15838651130517238495476739 23757976695775857743215109)
                  ·
                    refine ⟨4454620630457973326852833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23757976695775857743215109 4454620630457973326852833)
                    ·
                      refine ⟨3340965472843479995139625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454620630457973326852833 3340965472843479995139625)
                      ·
                        rfl

theorem cell23_6506507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4, 2].length) (baseStart_6506507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506507 prefixEnd_6506507 := by exact prefixLift 6506507
  have htrace : WordTrace (prefixWord ++ tailWord_6506507) baseStart_6506507 baseEnd_6506507 := by
    simpa [prefixWord, tailWord_6506507, baseEnd_6506507] using wordTrace_append hprefix tailTrace_6506507
  have hstable : (prefixWord ++ tailWord_6506507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506507).length < 2 ^ (prefixWord ++ tailWord_6506507).sum := by decide
  have hdescent : baseEnd_6506507 < baseStart_6506507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506510 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_6506510 : Nat := 118140960795 + 6506510 * 2 ^ 59
def prefixEnd_6506510 : Nat := 4983230072969 + 3 ^ 40 * 6506510 * 2
def baseEnd_6506510 : Nat := 3340967013285443483402111

theorem tailTrace_6506510 : CollatzResearch.WordTrace tailWord_6506510 prefixEnd_6506510 3340967013285443483402111 := by
  unfold tailWord_6506510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663989457254121035511623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158207943772021978856061989 29663989457254121035511623)
  ·
    refine ⟨44495984185881181553267435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29663989457254121035511623 44495984185881181553267435)
    ·
      refine ⟨66743976278821772329901153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44495984185881181553267435 66743976278821772329901153)
      ·
        refine ⟨50057982209116329247425865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66743976278821772329901153 50057982209116329247425865)
        ·
          refine ⟨37543486656837246935569399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50057982209116329247425865 37543486656837246935569399)
          ·
            refine ⟨56315229985255870403354099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37543486656837246935569399 56315229985255870403354099)
            ·
              refine ⟨84472844977883805605031149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56315229985255870403354099 84472844977883805605031149)
              ·
                refine ⟨31677316866706427101886681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84472844977883805605031149 31677316866706427101886681)
                ·
                  refine ⟨23757987650029820326415011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31677316866706427101886681 23757987650029820326415011)
                  ·
                    refine ⟨35636981475044730489622517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23757987650029820326415011 35636981475044730489622517)
                    ·
                      refine ⟨3340967013285443483402111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35636981475044730489622517 3340967013285443483402111)
                      ·
                        rfl

theorem cell23_6506510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_6506510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506510 prefixEnd_6506510 := by exact prefixLift 6506510
  have htrace : WordTrace (prefixWord ++ tailWord_6506510) baseStart_6506510 baseEnd_6506510 := by
    simpa [prefixWord, tailWord_6506510, baseEnd_6506510] using wordTrace_append hprefix tailTrace_6506510
  have hstable : (prefixWord ++ tailWord_6506510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506510).length < 2 ^ (prefixWord ++ tailWord_6506510).sum := by decide
  have hdescent : baseEnd_6506510 < baseStart_6506510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506520 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6506520 : Nat := 118140960795 + 6506520 * 2 ^ 59
def prefixEnd_6506520 : Nat := 4983230072969 + 3 ^ 40 * 6506520 * 2
def baseEnd_6506520 : Nat := 3340972148091988444277065

theorem tailTrace_6506520 : CollatzResearch.WordTrace tailWord_6506520 prefixEnd_6506520 3340972148091988444277065 := by
  unfold tailWord_6506520
  simp only [CollatzResearch.WordTrace]
  refine ⟨118656140193998369995978507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158208186925331159994638009 118656140193998369995978507)
  ·
    refine ⟨177984210290997554993967761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118656140193998369995978507 177984210290997554993967761)
    ·
      refine ⟨133488157718248166245475821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177984210290997554993967761 133488157718248166245475821)
      ·
        refine ⟨50058059144343062342053433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133488157718248166245475821 50058059144343062342053433)
        ·
          refine ⟨37543544358257296756540075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50058059144343062342053433 37543544358257296756540075)
          ·
            refine ⟨56315316537385945134810113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37543544358257296756540075 56315316537385945134810113)
            ·
              refine ⟨42236487403039458851107585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56315316537385945134810113 42236487403039458851107585)
              ·
                refine ⟨31677365552279594138330689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42236487403039458851107585 31677365552279594138330689)
                ·
                  refine ⟨23758024164209695603748017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31677365552279594138330689 23758024164209695603748017)
                  ·
                    refine ⟨17818518123157271702811013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23758024164209695603748017 17818518123157271702811013)
                    ·
                      refine ⟨3340972148091988444277065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17818518123157271702811013 3340972148091988444277065)
                      ·
                        rfl

theorem cell23_6506520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6506520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506520 prefixEnd_6506520 := by exact prefixLift 6506520
  have htrace : WordTrace (prefixWord ++ tailWord_6506520) baseStart_6506520 baseEnd_6506520 := by
    simpa [prefixWord, tailWord_6506520, baseEnd_6506520] using wordTrace_append hprefix tailTrace_6506520
  have hstable : (prefixWord ++ tailWord_6506520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506520).length < 2 ^ (prefixWord ++ tailWord_6506520).sum := by decide
  have hdescent : baseEnd_6506520 < baseStart_6506520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506530 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_6506530 : Nat := 118140960795 + 6506530 * 2 ^ 59
def prefixEnd_6506530 : Nat := 4983230072969 + 3 ^ 40 * 6506530 * 2
def baseEnd_6506530 : Nat := 371219698099837045016891

theorem tailTrace_6506530 : CollatzResearch.WordTrace tailWord_6506530 prefixEnd_6506530 371219698099837045016891 := by
  unfold tailWord_6506530
  simp only [CollatzResearch.WordTrace]
  refine ⟨59328161279490127924955261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158208430078640341133214029 59328161279490127924955261)
  ·
    refine ⟨22248060479808797971858223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59328161279490127924955261 22248060479808797971858223)
    ·
      refine ⟨33372090719713196957787335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22248060479808797971858223 33372090719713196957787335)
      ·
        refine ⟨50058136079569795436681003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33372090719713196957787335 50058136079569795436681003)
        ·
          refine ⟨75087204119354693155021505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50058136079569795436681003 75087204119354693155021505)
          ·
            refine ⟨56315403089516019866266129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75087204119354693155021505 56315403089516019866266129)
            ·
              refine ⟨42236552317137014899699597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56315403089516019866266129 42236552317137014899699597)
              ·
                refine ⟨15838707118926380587387349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42236552317137014899699597 15838707118926380587387349)
                ·
                  refine ⟨371219698099837045016891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15838707118926380587387349 371219698099837045016891)
                  ·
                    rfl

theorem cell23_6506530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_6506530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506530 prefixEnd_6506530 := by exact prefixLift 6506530
  have htrace : WordTrace (prefixWord ++ tailWord_6506530) baseStart_6506530 baseEnd_6506530 := by
    simpa [prefixWord, tailWord_6506530, baseEnd_6506530] using wordTrace_append hprefix tailTrace_6506530
  have hstable : (prefixWord ++ tailWord_6506530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506530).length < 2 ^ (prefixWord ++ tailWord_6506530).sum := by decide
  have hdescent : baseEnd_6506530 < baseStart_6506530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506560 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 7]
def baseStart_6506560 : Nat := 118140960795 + 6506560 * 2 ^ 59
def prefixEnd_6506560 : Nat := 4983230072969 + 3 ^ 40 * 6506560 * 2
def baseEnd_6506560 : Nat := 1113664229106056095925627

theorem tailTrace_6506560 : CollatzResearch.WordTrace tailWord_6506560 prefixEnd_6506560 1113664229106056095925627 := by
  unfold tailWord_6506560
  simp only [CollatzResearch.WordTrace]
  refine ⟨118656869653925913411706567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158209159538567884548942089 118656869653925913411706567)
  ·
    refine ⟨177985304480888870117559851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118656869653925913411706567 177985304480888870117559851)
    ·
      refine ⟨266977956721333305176339777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177985304480888870117559851 266977956721333305176339777)
      ·
        refine ⟨200233467540999978882254833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266977956721333305176339777 200233467540999978882254833)
        ·
          refine ⟨150175100655749984161691125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200233467540999978882254833 150175100655749984161691125)
          ·
            refine ⟨14078915686476561015158543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150175100655749984161691125 14078915686476561015158543)
            ·
              refine ⟨21118373529714841522737815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14078915686476561015158543 21118373529714841522737815)
              ·
                refine ⟨31677560294572262284106723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21118373529714841522737815 31677560294572262284106723)
                ·
                  refine ⟨47516340441858393426160085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31677560294572262284106723 47516340441858393426160085)
                  ·
                    refine ⟨1113664229106056095925627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47516340441858393426160085 1113664229106056095925627)
                    ·
                      rfl

theorem cell23_6506560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_6506560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506560 prefixEnd_6506560 := by exact prefixLift 6506560
  have htrace : WordTrace (prefixWord ++ tailWord_6506560) baseStart_6506560 baseEnd_6506560 := by
    simpa [prefixWord, tailWord_6506560, baseEnd_6506560] using wordTrace_append hprefix tailTrace_6506560
  have hstable : (prefixWord ++ tailWord_6506560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506560).length < 2 ^ (prefixWord ++ tailWord_6506560).sum := by decide
  have hdescent : baseEnd_6506560 < baseStart_6506560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506607 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 3, 4]
def baseStart_6506607 : Nat := 118140960795 + 6506607 * 2 ^ 59
def prefixEnd_6506607 : Nat := 4983230072969 + 3 ^ 40 * 6506607 * 2
def baseEnd_6506607 : Nat := 1113672273636309867963055

theorem tailTrace_6506607 : CollatzResearch.WordTrace tailWord_6506607 prefixEnd_6506607 1113672273636309867963055 := by
  unfold tailWord_6506607
  simp only [CollatzResearch.WordTrace]
  refine ⟨237315453538681553850374075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158210302359121035900249383 237315453538681553850374075)
  ·
    refine ⟨355973180308022330775561113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237315453538681553850374075 355973180308022330775561113)
    ·
      refine ⟨266979885231016748081670835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355973180308022330775561113 266979885231016748081670835)
      ·
        refine ⟨400469827846525122122506253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266979885231016748081670835 400469827846525122122506253)
        ·
          refine ⟨150176185442446920795939845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400469827846525122122506253 150176185442446920795939845)
          ·
            refine ⟨28158034770458797649238721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150176185442446920795939845 28158034770458797649238721)
            ·
              refine ⟨21118526077844098236929041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28158034770458797649238721 21118526077844098236929041)
              ·
                refine ⟨15838894558383073677696781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21118526077844098236929041 15838894558383073677696781)
                ·
                  refine ⟨5939585459393652629136293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15838894558383073677696781 5939585459393652629136293)
                  ·
                    refine ⟨1113672273636309867963055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5939585459393652629136293 1113672273636309867963055)
                    ·
                      rfl

theorem cell23_6506607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_6506607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506607 prefixEnd_6506607 := by exact prefixLift 6506607
  have htrace : WordTrace (prefixWord ++ tailWord_6506607) baseStart_6506607 baseEnd_6506607 := by
    simpa [prefixWord, tailWord_6506607, baseEnd_6506607] using wordTrace_append hprefix tailTrace_6506607
  have hstable : (prefixWord ++ tailWord_6506607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506607).length < 2 ^ (prefixWord ++ tailWord_6506607).sum := by decide
  have hdescent : baseEnd_6506607 < baseStart_6506607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506617 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_6506617 : Nat := 118140960795 + 6506617 * 2 ^ 59
def prefixEnd_6506617 : Nat := 4983230072969 + 3 ^ 40 * 6506617 * 2
def baseEnd_6506617 : Nat := 3341021955715474564764119

theorem tailTrace_6506617 : CollatzResearch.WordTrace tailWord_6506617 prefixEnd_6506617 3341021955715474564764119 := by
  unfold tailWord_6506617
  simp only [CollatzResearch.WordTrace]
  refine ⟨237315818268645325558238105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158210545512430217038825403 237315818268645325558238105)
  ·
    refine ⟨177986863701483994168678579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237315818268645325558238105 177986863701483994168678579)
    ·
      refine ⟨266980295552225991253017869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177986863701483994168678579 266980295552225991253017869)
      ·
        refine ⟨100117610832084746719881701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266980295552225991253017869 100117610832084746719881701)
        ·
          refine ⟨18772052031015890009977819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100117610832084746719881701 18772052031015890009977819)
          ·
            refine ⟨28158078046523835014966729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18772052031015890009977819 28158078046523835014966729)
            ·
              refine ⟨21118558534892876261225047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28158078046523835014966729 21118558534892876261225047)
              ·
                refine ⟨31677837802339314391837571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21118558534892876261225047 31677837802339314391837571)
                ·
                  refine ⟨47516756703508971587756357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31677837802339314391837571 47516756703508971587756357)
                  ·
                    refine ⟨8909391881907932172704317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47516756703508971587756357 8909391881907932172704317)
                    ·
                      refine ⟨3341021955715474564764119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909391881907932172704317 3341021955715474564764119)
                      ·
                        rfl

theorem cell23_6506617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_6506617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506617 prefixEnd_6506617 := by exact prefixLift 6506617
  have htrace : WordTrace (prefixWord ++ tailWord_6506617) baseStart_6506617 baseEnd_6506617 := by
    simpa [prefixWord, tailWord_6506617, baseEnd_6506617] using wordTrace_append hprefix tailTrace_6506617
  have hstable : (prefixWord ++ tailWord_6506617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506617).length < 2 ^ (prefixWord ++ tailWord_6506617).sum := by decide
  have hdescent : baseEnd_6506617 < baseStart_6506617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506620 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 8]
def baseStart_6506620 : Nat := 118140960795 + 6506620 * 2 ^ 59
def prefixEnd_6506620 : Nat := 4983230072969 + 3 ^ 40 * 6506620 * 2
def baseEnd_6506620 : Nat := 371224832906382005891845

theorem tailTrace_6506620 : CollatzResearch.WordTrace tailWord_6506620 prefixEnd_6506620 371224832906382005891845 := by
  unfold tailWord_6506620
  simp only [CollatzResearch.WordTrace]
  refine ⟨118657963843817228535298657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158210618458422971380398209 118657963843817228535298657)
  ·
    refine ⟨88993472882862921401473993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118657963843817228535298657 88993472882862921401473993)
    ·
      refine ⟨66745104662147191051105495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88993472882862921401473993 66745104662147191051105495)
      ·
        refine ⟨100117656993220786576658243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66745104662147191051105495 100117656993220786576658243)
        ·
          refine ⟨150176485489831179864987365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100117656993220786576658243 150176485489831179864987365)
          ·
            refine ⟨28158091029343346224685131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150176485489831179864987365 28158091029343346224685131)
            ·
              refine ⟨42237136544015019337027697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28158091029343346224685131 42237136544015019337027697)
              ·
                refine ⟨31677852408011264502770773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42237136544015019337027697 31677852408011264502770773)
                ·
                  refine ⟨371224832906382005891845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31677852408011264502770773 371224832906382005891845)
                  ·
                    rfl

theorem cell23_6506620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_6506620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506620 prefixEnd_6506620 := by exact prefixLift 6506620
  have htrace : WordTrace (prefixWord ++ tailWord_6506620) baseStart_6506620 baseEnd_6506620 := by
    simpa [prefixWord, tailWord_6506620, baseEnd_6506620] using wordTrace_append hprefix tailTrace_6506620
  have hstable : (prefixWord ++ tailWord_6506620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506620).length < 2 ^ (prefixWord ++ tailWord_6506620).sum := by decide
  have hdescent : baseEnd_6506620 < baseStart_6506620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506634 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_6506634 : Nat := 118140960795 + 6506634 * 2 ^ 59
def prefixEnd_6506634 : Nat := 4983230072969 + 3 ^ 40 * 6506634 * 2
def baseEnd_6506634 : Nat := 3341030684886600998251541

theorem tailTrace_6506634 : CollatzResearch.WordTrace tailWord_6506634 prefixEnd_6506634 3341030684886600998251541 := by
  unfold tailWord_6506634
  simp only [CollatzResearch.WordTrace]
  refine ⟨59329109577395934365401739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158210958873055824974404637 59329109577395934365401739)
  ·
    refine ⟨88993664366093901548102609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59329109577395934365401739 88993664366093901548102609)
    ·
      refine ⟨66745248274570426161076957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88993664366093901548102609 66745248274570426161076957)
      ·
        refine ⟨25029468102963909810403859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66745248274570426161076957 25029468102963909810403859)
        ·
          refine ⟨37544202154445864715605789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25029468102963909810403859 37544202154445864715605789)
          ·
            refine ⟨14079075807917199268352171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37544202154445864715605789 14079075807917199268352171)
            ·
              refine ⟨21118613711875798902528257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14079075807917199268352171 21118613711875798902528257)
              ·
                refine ⟨15838960283906849176896193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21118613711875798902528257 15838960283906849176896193)
                ·
                  refine ⟨11879220212930136882672145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15838960283906849176896193 11879220212930136882672145)
                  ·
                    refine ⟨8909415159697602662004109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11879220212930136882672145 8909415159697602662004109)
                    ·
                      refine ⟨3341030684886600998251541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909415159697602662004109 3341030684886600998251541)
                      ·
                        rfl

theorem cell23_6506634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_6506634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506634 prefixEnd_6506634 := by exact prefixLift 6506634
  have htrace : WordTrace (prefixWord ++ tailWord_6506634) baseStart_6506634 baseEnd_6506634 := by
    simpa [prefixWord, tailWord_6506634, baseEnd_6506634] using wordTrace_append hprefix tailTrace_6506634
  have hstable : (prefixWord ++ tailWord_6506634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506634).length < 2 ^ (prefixWord ++ tailWord_6506634).sum := by decide
  have hdescent : baseEnd_6506634 < baseStart_6506634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506681 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6506681 : Nat := 118140960795 + 6506681 * 2 ^ 59
def prefixEnd_6506681 : Nat := 4983230072969 + 3 ^ 40 * 6506681 * 2
def baseEnd_6506681 : Nat := 3341054818477362314363825

theorem tailTrace_6506681 : CollatzResearch.WordTrace tailWord_6506681 prefixEnd_6506681 3341054818477362314363825 := by
  unfold tailWord_6506681
  simp only [CollatzResearch.WordTrace]
  refine ⟨237318152540413464488567897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158212101693608976325711931 237318152540413464488567897)
  ·
    refine ⟨177988614405310098366425923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237318152540413464488567897 177988614405310098366425923)
    ·
      refine ⟨266982921607965147549638885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177988614405310098366425923 266982921607965147549638885)
      ·
        refine ⟨50059297801493465165557291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266982921607965147549638885 50059297801493465165557291)
        ·
          refine ⟨75088946702240197748335937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50059297801493465165557291 75088946702240197748335937)
          ·
            refine ⟨56316710026680148311251953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75088946702240197748335937 56316710026680148311251953)
            ·
              refine ⟨42237532520010111233438965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56316710026680148311251953 42237532520010111233438965)
              ·
                refine ⟨3959768673750947928134903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42237532520010111233438965 3959768673750947928134903)
                ·
                  refine ⟨5939653010626421892202355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959768673750947928134903 5939653010626421892202355)
                  ·
                    refine ⟨8909479515939632838303533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5939653010626421892202355 8909479515939632838303533)
                    ·
                      refine ⟨3341054818477362314363825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909479515939632838303533 3341054818477362314363825)
                      ·
                        rfl

theorem cell23_6506681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6506681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506681 prefixEnd_6506681 := by exact prefixLift 6506681
  have htrace : WordTrace (prefixWord ++ tailWord_6506681) baseStart_6506681 baseEnd_6506681 := by
    simpa [prefixWord, tailWord_6506681, baseEnd_6506681] using wordTrace_append hprefix tailTrace_6506681
  have hstable : (prefixWord ++ tailWord_6506681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506681).length < 2 ^ (prefixWord ++ tailWord_6506681).sum := by decide
  have hdescent : baseEnd_6506681 < baseStart_6506681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506704 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2]
def baseStart_6506704 : Nat := 118140960795 + 6506704 * 2 ^ 59
def prefixEnd_6506704 : Nat := 4983230072969 + 3 ^ 40 * 6506704 * 2
def baseEnd_6506704 : Nat := 3341066628532415724376219

theorem tailTrace_6506704 : CollatzResearch.WordTrace tailWord_6506704 prefixEnd_6506704 3341066628532415724376219 := by
  unfold tailWord_6506704
  simp only [CollatzResearch.WordTrace]
  refine ⟨118659495709665069708327583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158212660946220092944436777 118659495709665069708327583)
  ·
    refine ⟨177989243564497604562491375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118659495709665069708327583 177989243564497604562491375)
    ·
      refine ⟨266983865346746406843737063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177989243564497604562491375 266983865346746406843737063)
      ·
        refine ⟨400475798020119610265605595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266983865346746406843737063 400475798020119610265605595)
        ·
          refine ⟨600713697030179415398408393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400475798020119610265605595 600713697030179415398408393)
          ·
            refine ⟨450535272772634561548806295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600713697030179415398408393 450535272772634561548806295)
            ·
              refine ⟨675802909158951842323209443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450535272772634561548806295 675802909158951842323209443)
              ·
                refine ⟨1013704363738427763484814165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675802909158951842323209443 1013704363738427763484814165)
                ·
                  refine ⟨5939674006279850176668833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1013704363738427763484814165 5939674006279850176668833)
                  ·
                    refine ⟨4454755504709887632501625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5939674006279850176668833 4454755504709887632501625)
                    ·
                      refine ⟨3341066628532415724376219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454755504709887632501625 3341066628532415724376219)
                      ·
                        rfl

theorem cell23_6506704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 2, 2].length) (baseStart_6506704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506704 prefixEnd_6506704 := by exact prefixLift 6506704
  have htrace : WordTrace (prefixWord ++ tailWord_6506704) baseStart_6506704 baseEnd_6506704 := by
    simpa [prefixWord, tailWord_6506704, baseEnd_6506704] using wordTrace_append hprefix tailTrace_6506704
  have hstable : (prefixWord ++ tailWord_6506704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506704).length < 2 ^ (prefixWord ++ tailWord_6506704).sum := by decide
  have hdescent : baseEnd_6506704 < baseStart_6506704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506714 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_6506714 : Nat := 118140960795 + 6506714 * 2 ^ 59
def prefixEnd_6506714 : Nat := 4983230072969 + 3 ^ 40 * 6506714 * 2
def baseEnd_6506714 : Nat := 1113690587779653561750391

theorem tailTrace_6506714 : CollatzResearch.WordTrace tailWord_6506714 prefixEnd_6506714 1113690587779653561750391 := by
  unfold tailWord_6506714
  simp only [CollatzResearch.WordTrace]
  refine ⟨59329839037323477781129799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158212904099529274083012797 59329839037323477781129799)
  ·
    refine ⟨88994758555985216671694699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59329839037323477781129799 88994758555985216671694699)
    ·
      refine ⟨133492137833977825007542049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88994758555985216671694699 133492137833977825007542049)
      ·
        refine ⟨100119103375483368755656537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133492137833977825007542049 100119103375483368755656537)
        ·
          refine ⟨75089327531612526566742403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100119103375483368755656537 75089327531612526566742403)
          ·
            refine ⟨112633991297418789850113605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75089327531612526566742403 112633991297418789850113605)
            ·
              refine ⟨21118873368266023096896301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112633991297418789850113605 21118873368266023096896301)
              ·
                refine ⟨7919577513099758661336113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21118873368266023096896301 7919577513099758661336113)
                ·
                  refine ⟨5939683134824818996002085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7919577513099758661336113 5939683134824818996002085)
                  ·
                    refine ⟨1113690587779653561750391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5939683134824818996002085 1113690587779653561750391)
                    ·
                      rfl

theorem cell23_6506714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_6506714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506714 prefixEnd_6506714 := by exact prefixLift 6506714
  have htrace : WordTrace (prefixWord ++ tailWord_6506714) baseStart_6506714 baseEnd_6506714 := by
    simpa [prefixWord, tailWord_6506714, baseEnd_6506714] using wordTrace_append hprefix tailTrace_6506714
  have hstable : (prefixWord ++ tailWord_6506714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506714).length < 2 ^ (prefixWord ++ tailWord_6506714).sum := by decide
  have hdescent : baseEnd_6506714 < baseStart_6506714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506721 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_6506721 : Nat := 118140960795 + 6506721 * 2 ^ 59
def prefixEnd_6506721 : Nat := 4983230072969 + 3 ^ 40 * 6506721 * 2
def baseEnd_6506721 : Nat := 3341075357703542157863641

theorem tailTrace_6506721 : CollatzResearch.WordTrace tailWord_6506721 prefixEnd_6506721 3341075357703542157863641 := by
  unfold tailWord_6506721
  simp only [CollatzResearch.WordTrace]
  refine ⟨237319611460268551320024017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158213074306845700880016011 237319611460268551320024017)
  ·
    refine ⟨177989708595201413490018013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237319611460268551320024017 177989708595201413490018013)
    ·
      refine ⟨66746140723200530058756755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177989708595201413490018013 66746140723200530058756755)
      ·
        refine ⟨100119211084800795088135133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66746140723200530058756755 100119211084800795088135133)
        ·
          refine ⟨37544704156800298158050675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100119211084800795088135133 37544704156800298158050675)
          ·
            refine ⟨56317056235200447237076013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37544704156800298158050675 56317056235200447237076013)
            ·
              refine ⟨21118896088200167713903505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56317056235200447237076013 21118896088200167713903505)
              ·
                refine ⟨15839172066150125785427629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21118896088200167713903505 15839172066150125785427629)
                ·
                  refine ⟨5939689524806297169535361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15839172066150125785427629 5939689524806297169535361)
                  ·
                    refine ⟨4454767143604722877151521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5939689524806297169535361 4454767143604722877151521)
                    ·
                      refine ⟨3341075357703542157863641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454767143604722877151521 3341075357703542157863641)
                      ·
                        rfl

theorem cell23_6506721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_6506721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506721 prefixEnd_6506721 := by exact prefixLift 6506721
  have htrace : WordTrace (prefixWord ++ tailWord_6506721) baseStart_6506721 baseEnd_6506721 := by
    simpa [prefixWord, tailWord_6506721, baseEnd_6506721] using wordTrace_append hprefix tailTrace_6506721
  have hstable : (prefixWord ++ tailWord_6506721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506721).length < 2 ^ (prefixWord ++ tailWord_6506721).sum := by decide
  have hdescent : baseEnd_6506721 < baseStart_6506721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506724 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_6506724 : Nat := 118140960795 + 6506724 * 2 ^ 59
def prefixEnd_6506724 : Nat := 4983230072969 + 3 ^ 40 * 6506724 * 2
def baseEnd_6506724 : Nat := 3341076898145505646126127

theorem tailTrace_6506724 : CollatzResearch.WordTrace tailWord_6506724 prefixEnd_6506724 3341076898145505646126127 := by
  unfold tailWord_6506724
  simp only [CollatzResearch.WordTrace]
  refine ⟨118659860439628841416191613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158213147252838455221588817 118659860439628841416191613)
  ·
    refine ⟨44497447664860815531071855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118659860439628841416191613 44497447664860815531071855)
    ·
      refine ⟨66746171497291223296607783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44497447664860815531071855 66746171497291223296607783)
      ·
        refine ⟨100119257245936834944911675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66746171497291223296607783 100119257245936834944911675)
        ·
          refine ⟨150178885868905252417367513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100119257245936834944911675 150178885868905252417367513)
          ·
            refine ⟨112634164401678939313025635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150178885868905252417367513 112634164401678939313025635)
            ·
              refine ⟨168951246602518408969538453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112634164401678939313025635 168951246602518408969538453)
              ·
                refine ⟨7919589684493050420447115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168951246602518408969538453 7919589684493050420447115)
                ·
                  refine ⟨11879384526739575630670673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7919589684493050420447115 11879384526739575630670673)
                  ·
                    refine ⟨8909538395054681723003005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11879384526739575630670673 8909538395054681723003005)
                    ·
                      refine ⟨3341076898145505646126127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909538395054681723003005 3341076898145505646126127)
                      ·
                        rfl

theorem cell23_6506724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_6506724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506724 prefixEnd_6506724 := by exact prefixLift 6506724
  have htrace : WordTrace (prefixWord ++ tailWord_6506724) baseStart_6506724 baseEnd_6506724 := by
    simpa [prefixWord, tailWord_6506724, baseEnd_6506724] using wordTrace_append hprefix tailTrace_6506724
  have hstable : (prefixWord ++ tailWord_6506724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506724).length < 2 ^ (prefixWord ++ tailWord_6506724).sum := by decide
  have hdescent : baseEnd_6506724 < baseStart_6506724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506738 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_6506738 : Nat := 118140960795 + 6506738 * 2 ^ 59
def prefixEnd_6506738 : Nat := 4983230072969 + 3 ^ 40 * 6506738 * 2
def baseEnd_6506738 : Nat := 3341084086874668591351063

theorem tailTrace_6506738 : CollatzResearch.WordTrace tailWord_6506738 prefixEnd_6506738 3341084086874668591351063 := by
  unfold tailWord_6506738
  simp only [CollatzResearch.WordTrace]
  refine ⟨59330057875301740805848217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158213487667471308815595245 59330057875301740805848217)
  ·
    refine ⟨44497543406476305604386163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59330057875301740805848217 44497543406476305604386163)
    ·
      refine ⟨66746315109714458406579245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44497543406476305604386163 66746315109714458406579245)
      ·
        refine ⟨25029868166142921902467217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66746315109714458406579245 25029868166142921902467217)
        ·
          refine ⟨18772401124607191426850413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25029868166142921902467217 18772401124607191426850413)
          ·
            refine ⟨7039650421727696785068905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18772401124607191426850413 7039650421727696785068905)
            ·
              refine ⟨5279737816295772588801679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7039650421727696785068905 5279737816295772588801679)
              ·
                refine ⟨7919606724443658883202519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279737816295772588801679 7919606724443658883202519)
                ·
                  refine ⟨11879410086665488324803779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7919606724443658883202519 11879410086665488324803779)
                  ·
                    refine ⟨17819115129998232487205669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11879410086665488324803779 17819115129998232487205669)
                    ·
                      refine ⟨3341084086874668591351063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17819115129998232487205669 3341084086874668591351063)
                      ·
                        rfl

theorem cell23_6506738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_6506738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506738 prefixEnd_6506738 := by exact prefixLift 6506738
  have htrace : WordTrace (prefixWord ++ tailWord_6506738) baseStart_6506738 baseEnd_6506738 := by
    simpa [prefixWord, tailWord_6506738, baseEnd_6506738] using wordTrace_append hprefix tailTrace_6506738
  have hstable : (prefixWord ++ tailWord_6506738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506738).length < 2 ^ (prefixWord ++ tailWord_6506738).sum := by decide
  have hdescent : baseEnd_6506738 < baseStart_6506738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506807 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_6506807 : Nat := 118140960795 + 6506807 * 2 ^ 59
def prefixEnd_6506807 : Nat := 4983230072969 + 3 ^ 40 * 6506807 * 2
def baseEnd_6506807 : Nat := 3341119517039828821388245

theorem tailTrace_6506807 : CollatzResearch.WordTrace tailWord_6506807 prefixEnd_6506807 3341119517039828821388245 := by
  unfold tailWord_6506807
  simp only [CollatzResearch.WordTrace]
  refine ⟨237322748137956988007654675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158215165425304658671769783 237322748137956988007654675)
  ·
    refine ⟨355984122206935482011482013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237322748137956988007654675 355984122206935482011482013)
    ·
      refine ⟨133494045827600805754305755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355984122206935482011482013 133494045827600805754305755)
      ·
        refine ⟨200241068741401208631458633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133494045827600805754305755 200241068741401208631458633)
        ·
          refine ⟨150180801556050906473593975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200241068741401208631458633 150180801556050906473593975)
          ·
            refine ⟨225271202334076359710390963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150180801556050906473593975 225271202334076359710390963)
            ·
              refine ⟨337906803501114539565586445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225271202334076359710390963 337906803501114539565586445)
              ·
                refine ⟨126715051312917952337094917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337906803501114539565586445 126715051312917952337094917)
                ·
                  refine ⟨23759072121172116063205297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126715051312917952337094917 23759072121172116063205297)
                  ·
                    refine ⟨17819304090879087047403973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23759072121172116063205297 17819304090879087047403973)
                    ·
                      refine ⟨3341119517039828821388245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17819304090879087047403973 3341119517039828821388245)
                      ·
                        rfl

theorem cell23_6506807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_6506807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506807 prefixEnd_6506807 := by exact prefixLift 6506807
  have htrace : WordTrace (prefixWord ++ tailWord_6506807) baseStart_6506807 baseEnd_6506807 := by
    simpa [prefixWord, tailWord_6506807, baseEnd_6506807] using wordTrace_append hprefix tailTrace_6506807
  have hstable : (prefixWord ++ tailWord_6506807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506807).length < 2 ^ (prefixWord ++ tailWord_6506807).sum := by decide
  have hdescent : baseEnd_6506807 < baseStart_6506807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506828 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6506828 : Nat := 118140960795 + 6506828 * 2 ^ 59
def prefixEnd_6506828 : Nat := 4983230072969 + 3 ^ 40 * 6506828 * 2
def baseEnd_6506828 : Nat := 3341130300133573239225649

theorem tailTrace_6506828 : CollatzResearch.WordTrace tailWord_6506828 prefixEnd_6506828 3341130300133573239225649 := by
  unfold tailWord_6506828
  simp only [CollatzResearch.WordTrace]
  refine ⟨118661757035440454297084569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158215676047253939062779425 118661757035440454297084569)
  ·
    refine ⟨88996317776580340722813427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118661757035440454297084569 88996317776580340722813427)
    ·
      refine ⟨133494476664870511084220141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88996317776580340722813427 133494476664870511084220141)
      ·
        refine ⟨50060428749326441656582553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133494476664870511084220141 50060428749326441656582553)
        ·
          refine ⟨37545321561994831242436915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50060428749326441656582553 37545321561994831242436915)
          ·
            refine ⟨56317982342992246863655373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37545321561994831242436915 56317982342992246863655373)
            ·
              refine ⟨21119243378622092573870765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56317982342992246863655373 21119243378622092573870765)
              ·
                refine ⟨7919716266983284715201537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21119243378622092573870765 7919716266983284715201537)
                ·
                  refine ⟨5939787200237463536401153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7919716266983284715201537 5939787200237463536401153)
                  ·
                    refine ⟨4454840400178097652300865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5939787200237463536401153 4454840400178097652300865)
                    ·
                      refine ⟨3341130300133573239225649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454840400178097652300865 3341130300133573239225649)
                      ·
                        rfl

theorem cell23_6506828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6506828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506828 prefixEnd_6506828 := by exact prefixLift 6506828
  have htrace : WordTrace (prefixWord ++ tailWord_6506828) baseStart_6506828 baseEnd_6506828 := by
    simpa [prefixWord, tailWord_6506828, baseEnd_6506828] using wordTrace_append hprefix tailTrace_6506828
  have hstable : (prefixWord ++ tailWord_6506828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506828).length < 2 ^ (prefixWord ++ tailWord_6506828).sum := by decide
  have hdescent : baseEnd_6506828 < baseStart_6506828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506847 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 7]
def baseStart_6506847 : Nat := 118140960795 + 6506847 * 2 ^ 59
def prefixEnd_6506847 : Nat := 4983230072969 + 3 ^ 40 * 6506847 * 2
def baseEnd_6506847 : Nat := 1113713352088669554962687

theorem tailTrace_6506847 : CollatzResearch.WordTrace tailWord_6506847 prefixEnd_6506847 1113713352088669554962687 := by
  unfold tailWord_6506847
  simp only [CollatzResearch.WordTrace]
  refine ⟨237324207057812074839110795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158216138038541383226073863 237324207057812074839110795)
  ·
    refine ⟨355986310586718112258666193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237324207057812074839110795 355986310586718112258666193)
    ·
      refine ⟨266989732940038584193999645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355986310586718112258666193 266989732940038584193999645)
      ·
        refine ⟨100121149852514469072749867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266989732940038584193999645 100121149852514469072749867)
        ·
          refine ⟨150181724778771703609124801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100121149852514469072749867 150181724778771703609124801)
          ·
            refine ⟨112636293584078777706843601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150181724778771703609124801 112636293584078777706843601)
            ·
              refine ⟨84477220188059083280132701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112636293584078777706843601 84477220188059083280132701)
              ·
                refine ⟨31678957570522156230049763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84477220188059083280132701 31678957570522156230049763)
                ·
                  refine ⟨47518436355783234345074645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31678957570522156230049763 47518436355783234345074645)
                  ·
                    refine ⟨1113713352088669554962687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47518436355783234345074645 1113713352088669554962687)
                    ·
                      rfl

theorem cell23_6506847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_6506847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506847 prefixEnd_6506847 := by exact prefixLift 6506847
  have htrace : WordTrace (prefixWord ++ tailWord_6506847) baseStart_6506847 baseEnd_6506847 := by
    simpa [prefixWord, tailWord_6506847, baseEnd_6506847] using wordTrace_append hprefix tailTrace_6506847
  have hstable : (prefixWord ++ tailWord_6506847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506847).length < 2 ^ (prefixWord ++ tailWord_6506847).sum := by decide
  have hdescent : baseEnd_6506847 < baseStart_6506847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506857 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_6506857 : Nat := 118140960795 + 6506857 * 2 ^ 59
def prefixEnd_6506857 : Nat := 4983230072969 + 3 ^ 40 * 6506857 * 2
def baseEnd_6506857 : Nat := 3341145191072553625763015

theorem tailTrace_6506857 : CollatzResearch.WordTrace tailWord_6506857 prefixEnd_6506857 3341145191072553625763015 := by
  unfold tailWord_6506857
  simp only [CollatzResearch.WordTrace]
  refine ⟨237324571787775846546974825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158216381191850564364649883 237324571787775846546974825)
  ·
    refine ⟨177993428840831884910231119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237324571787775846546974825 177993428840831884910231119)
    ·
      refine ⟨266990143261247827365346679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177993428840831884910231119 266990143261247827365346679)
      ·
        refine ⟨400485214891871741048020019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266990143261247827365346679 400485214891871741048020019)
        ·
          refine ⟨600727822337807611572030029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400485214891871741048020019 600727822337807611572030029)
          ·
            refine ⟨225272933376677854339511261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600727822337807611572030029 225272933376677854339511261)
            ·
              refine ⟨84477350016254195377316723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225272933376677854339511261 84477350016254195377316723)
              ·
                refine ⟨126716025024381293065975085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84477350016254195377316723 126716025024381293065975085)
                ·
                  refine ⟨47518509384142984899740657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126716025024381293065975085 47518509384142984899740657)
                  ·
                    refine ⟨35638882038107238674805493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47518509384142984899740657 35638882038107238674805493)
                    ·
                      refine ⟨3341145191072553625763015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35638882038107238674805493 3341145191072553625763015)
                      ·
                        rfl

theorem cell23_6506857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_6506857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506857 prefixEnd_6506857 := by exact prefixLift 6506857
  have htrace : WordTrace (prefixWord ++ tailWord_6506857) baseStart_6506857 baseEnd_6506857 := by
    simpa [prefixWord, tailWord_6506857, baseEnd_6506857] using wordTrace_append hprefix tailTrace_6506857
  have hstable : (prefixWord ++ tailWord_6506857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506857).length < 2 ^ (prefixWord ++ tailWord_6506857).sum := by decide
  have hdescent : baseEnd_6506857 < baseStart_6506857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506864 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 2, 5]
def baseStart_6506864 : Nat := 118140960795 + 6506864 * 2 ^ 59
def prefixEnd_6506864 : Nat := 4983230072969 + 3 ^ 40 * 6506864 * 2
def baseEnd_6506864 : Nat := 1113716261812378366125161

theorem tailTrace_6506864 : CollatzResearch.WordTrace tailWord_6506864 prefixEnd_6506864 1113716261812378366125161 := by
  unfold tailWord_6506864
  simp only [CollatzResearch.WordTrace]
  refine ⟨118662413549375243371239823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158216551399166991161653097 118662413549375243371239823)
  ·
    refine ⟨177993620324062865056859735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118662413549375243371239823 177993620324062865056859735)
    ·
      refine ⟨266990430486094297585289603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177993620324062865056859735 266990430486094297585289603)
      ·
        refine ⟨400485645729141446377934405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266990430486094297585289603 400485645729141446377934405)
        ·
          refine ⟨75091058574214021195862701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400485645729141446377934405 75091058574214021195862701)
          ·
            refine ⟨28159146965330257948448513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75091058574214021195862701 28159146965330257948448513)
            ·
              refine ⟨21119360223997693461336385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28159146965330257948448513 21119360223997693461336385)
              ·
                refine ⟨15839520167998270096002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21119360223997693461336385 15839520167998270096002289)
                ·
                  refine ⟨11879640125998702572001717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15839520167998270096002289 11879640125998702572001717)
                  ·
                    refine ⟨1113716261812378366125161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11879640125998702572001717 1113716261812378366125161)
                    ·
                      rfl

theorem cell23_6506864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_6506864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506864 prefixEnd_6506864 := by exact prefixLift 6506864
  have htrace : WordTrace (prefixWord ++ tailWord_6506864) baseStart_6506864 baseEnd_6506864 := by
    simpa [prefixWord, tailWord_6506864, baseEnd_6506864] using wordTrace_append hprefix tailTrace_6506864
  have hstable : (prefixWord ++ tailWord_6506864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506864).length < 2 ^ (prefixWord ++ tailWord_6506864).sum := by decide
  have hdescent : baseEnd_6506864 < baseStart_6506864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506884 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_6506884 : Nat := 118140960795 + 6506884 * 2 ^ 59
def prefixEnd_6506884 : Nat := 4983230072969 + 3 ^ 40 * 6506884 * 2
def baseEnd_6506884 : Nat := 3341159055050225020125391

theorem tailTrace_6506884 : CollatzResearch.WordTrace tailWord_6506884 prefixEnd_6506884 3341159055050225020125391 := by
  unfold tailWord_6506884
  simp only [CollatzResearch.WordTrace]
  refine ⟨118662778279339015079103853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158217037705785353438805137 118662778279339015079103853)
  ·
    refine ⟨44498541854752130654663945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118662778279339015079103853 44498541854752130654663945)
    ·
      refine ⟨33373906391064097990997959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44498541854752130654663945 33373906391064097990997959)
      ·
        refine ⟨50060859586596146986496939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33373906391064097990997959 50060859586596146986496939)
        ·
          refine ⟨75091289379894220479745409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50060859586596146986496939 75091289379894220479745409)
          ·
            refine ⟨56318467034920665359809057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75091289379894220479745409 56318467034920665359809057)
            ·
              refine ⟨42238850276190499019856793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56318467034920665359809057 42238850276190499019856793)
              ·
                refine ⟨31679137707142874264892595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42238850276190499019856793 31679137707142874264892595)
                ·
                  refine ⟨47518706560714311397338893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31679137707142874264892595 47518706560714311397338893)
                  ·
                    refine ⟨17819514960267866774002085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47518706560714311397338893 17819514960267866774002085)
                    ·
                      refine ⟨3341159055050225020125391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17819514960267866774002085 3341159055050225020125391)
                      ·
                        rfl

theorem cell23_6506884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_6506884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506884 prefixEnd_6506884 := by exact prefixLift 6506884
  have htrace : WordTrace (prefixWord ++ tailWord_6506884) baseStart_6506884 baseEnd_6506884 := by
    simpa [prefixWord, tailWord_6506884, baseEnd_6506884] using wordTrace_append hprefix tailTrace_6506884
  have hstable : (prefixWord ++ tailWord_6506884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506884).length < 2 ^ (prefixWord ++ tailWord_6506884).sum := by decide
  have hdescent : baseEnd_6506884 < baseStart_6506884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506897 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_6506897 : Nat := 118140960795 + 6506897 * 2 ^ 59
def prefixEnd_6506897 : Nat := 4983230072969 + 3 ^ 40 * 6506897 * 2
def baseEnd_6506897 : Nat := 3341165730298733469262831

theorem tailTrace_6506897 : CollatzResearch.WordTrace tailWord_6506897 prefixEnd_6506897 3341165730298733469262831 := by
  unfold tailWord_6506897
  simp only [CollatzResearch.WordTrace]
  refine ⟨237326030707630933378430945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158217353805087288918953963 237326030707630933378430945)
  ·
    refine ⟨177994523030723200033823209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237326030707630933378430945 177994523030723200033823209)
    ·
      refine ⟨133495892273042400025367407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177994523030723200033823209 133495892273042400025367407)
      ·
        refine ⟨200243838409563600038051111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133495892273042400025367407 200243838409563600038051111)
        ·
          refine ⟨300365757614345400057076667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200243838409563600038051111 300365757614345400057076667)
          ·
            refine ⟨450548636421518100085615001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300365757614345400057076667 450548636421518100085615001)
            ·
              refine ⟨337911477316138575064211251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450548636421518100085615001 337911477316138575064211251)
              ·
                refine ⟨506867215974207862596316877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337911477316138575064211251 506867215974207862596316877)
                ·
                  refine ⟨190075205990327948473618829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506867215974207862596316877 190075205990327948473618829)
                  ·
                    refine ⟨71278202246372980677607061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190075205990327948473618829 71278202246372980677607061)
                    ·
                      refine ⟨3341165730298733469262831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71278202246372980677607061 3341165730298733469262831)
                      ·
                        rfl

theorem cell23_6506897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_6506897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506897 prefixEnd_6506897 := by exact prefixLift 6506897
  have htrace : WordTrace (prefixWord ++ tailWord_6506897) baseStart_6506897 baseEnd_6506897 := by
    simpa [prefixWord, tailWord_6506897, baseEnd_6506897] using wordTrace_append hprefix tailTrace_6506897
  have hstable : (prefixWord ++ tailWord_6506897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506897).length < 2 ^ (prefixWord ++ tailWord_6506897).sum := by decide
  have hdescent : baseEnd_6506897 < baseStart_6506897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506914 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_6506914 : Nat := 118140960795 + 6506914 * 2 ^ 59
def prefixEnd_6506914 : Nat := 4983230072969 + 3 ^ 40 * 6506914 * 2
def baseEnd_6506914 : Nat := 3341174459469859902750253

theorem tailTrace_6506914 : CollatzResearch.WordTrace tailWord_6506914 prefixEnd_6506914 3341174459469859902750253 := by
  unfold tailWord_6506914
  simp only [CollatzResearch.WordTrace]
  refine ⟨59331662687142336320449949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158217767165712896854533197 59331662687142336320449949)
  ·
    refine ⟨22249373507678376120168731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59331662687142336320449949 22249373507678376120168731)
    ·
      refine ⟨33374060261517564180253097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22249373507678376120168731 33374060261517564180253097)
      ·
        refine ⟨25030545196138173135189823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33374060261517564180253097 25030545196138173135189823)
        ·
          refine ⟨37545817794207259702784735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25030545196138173135189823 37545817794207259702784735)
          ·
            refine ⟨56318726691310889554177103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37545817794207259702784735 56318726691310889554177103)
            ·
              refine ⟨84478090036966334331265655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56318726691310889554177103 84478090036966334331265655)
              ·
                refine ⟨126717135055449501496898483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84478090036966334331265655 126717135055449501496898483)
                ·
                  refine ⟨190075702583174252245347725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126717135055449501496898483 190075702583174252245347725)
                  ·
                    refine ⟨71278388468690344592005397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190075702583174252245347725 71278388468690344592005397)
                    ·
                      refine ⟨3341174459469859902750253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71278388468690344592005397 3341174459469859902750253)
                      ·
                        rfl

theorem cell23_6506914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_6506914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506914 prefixEnd_6506914 := by exact prefixLift 6506914
  have htrace : WordTrace (prefixWord ++ tailWord_6506914) baseStart_6506914 baseEnd_6506914 := by
    simpa [prefixWord, tailWord_6506914, baseEnd_6506914] using wordTrace_append hprefix tailTrace_6506914
  have hstable : (prefixWord ++ tailWord_6506914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506914).length < 2 ^ (prefixWord ++ tailWord_6506914).sum := by decide
  have hdescent : baseEnd_6506914 < baseStart_6506914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6506961 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_6506961 : Nat := 118140960795 + 6506961 * 2 ^ 59
def prefixEnd_6506961 : Nat := 4983230072969 + 3 ^ 40 * 6506961 * 2
def baseEnd_6506961 : Nat := 3341198593060621218862537

theorem tailTrace_6506961 : CollatzResearch.WordTrace tailWord_6506961 prefixEnd_6506961 3341198593060621218862537 := by
  unfold tailWord_6506961
  simp only [CollatzResearch.WordTrace]
  refine ⟨237328364979399072308760737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158218909986266048205840491 237328364979399072308760737)
  ·
    refine ⟨177996273734549304231570553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237328364979399072308760737 177996273734549304231570553)
    ·
      refine ⟨133497205300911978173677915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177996273734549304231570553 133497205300911978173677915)
      ·
        refine ⟨200245807951367967260516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133497205300911978173677915 200245807951367967260516873)
        ·
          refine ⟨150184355963525975445387655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200245807951367967260516873 150184355963525975445387655)
          ·
            refine ⟨225276533945288963168081483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150184355963525975445387655 225276533945288963168081483)
            ·
              refine ⟨337914800917933444752122225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225276533945288963168081483 337914800917933444752122225)
              ·
                refine ⟨253436100688450083564091669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337914800917933444752122225 253436100688450083564091669)
                ·
                  refine ⟨11879817219771097667066797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 253436100688450083564091669 11879817219771097667066797)
                  ·
                    refine ⟨4454931457414161625150049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11879817219771097667066797 4454931457414161625150049)
                    ·
                      refine ⟨3341198593060621218862537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4454931457414161625150049 3341198593060621218862537)
                      ·
                        rfl

theorem cell23_6506961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_6506961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6506961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6506961 prefixEnd_6506961 := by exact prefixLift 6506961
  have htrace : WordTrace (prefixWord ++ tailWord_6506961) baseStart_6506961 baseEnd_6506961 := by
    simpa [prefixWord, tailWord_6506961, baseEnd_6506961] using wordTrace_append hprefix tailTrace_6506961
  have hstable : (prefixWord ++ tailWord_6506961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6506961).length < 2 ^ (prefixWord ++ tailWord_6506961).sum := by decide
  have hdescent : baseEnd_6506961 < baseStart_6506961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6506961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507011 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3]
def baseStart_6507011 : Nat := 118140960795 + 6507011 * 2 ^ 59
def prefixEnd_6507011 : Nat := 4983230072969 + 3 ^ 40 * 6507011 * 2
def baseEnd_6507011 : Nat := 3341224267093346023237307

theorem tailTrace_6507011 : CollatzResearch.WordTrace tailWord_6507011 prefixEnd_6507011 3341224267093346023237307 := by
  unfold tailWord_6507011
  simp only [CollatzResearch.WordTrace]
  refine ⟨237330188629217930848080887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158220125752811953898720591 237330188629217930848080887)
  ·
    refine ⟨355995282943826896272121331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237330188629217930848080887 355995282943826896272121331)
    ·
      refine ⟨533992924415740344408181997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355995282943826896272121331 533992924415740344408181997)
      ·
        refine ⟨200247346655902629153068249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533992924415740344408181997 200247346655902629153068249)
        ·
          refine ⟨150185509991926971864801187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200247346655902629153068249 150185509991926971864801187)
          ·
            refine ⟨225278264987890457797201781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150185509991926971864801187 225278264987890457797201781)
            ·
              refine ⟨21119837342614730418487667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225278264987890457797201781 21119837342614730418487667)
              ·
                refine ⟨31679756013922095627731501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21119837342614730418487667 31679756013922095627731501)
                ·
                  refine ⟨11879908505220785860399313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31679756013922095627731501 11879908505220785860399313)
                  ·
                    refine ⟨8909931378915589395299485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11879908505220785860399313 8909931378915589395299485)
                    ·
                      refine ⟨3341224267093346023237307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909931378915589395299485 3341224267093346023237307)
                      ·
                        rfl

theorem cell23_6507011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_6507011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507011 prefixEnd_6507011 := by exact prefixLift 6507011
  have htrace : WordTrace (prefixWord ++ tailWord_6507011) baseStart_6507011 baseEnd_6507011 := by
    simpa [prefixWord, tailWord_6507011, baseEnd_6507011] using wordTrace_append hprefix tailTrace_6507011
  have hstable : (prefixWord ++ tailWord_6507011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507011).length < 2 ^ (prefixWord ++ tailWord_6507011).sum := by decide
  have hdescent : baseEnd_6507011 < baseStart_6507011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507031 : List Nat := [1, 1, 3, 6, 1, 11]
def baseStart_6507031 : Nat := 118140960795 + 6507031 * 2 ^ 59
def prefixEnd_6507031 : Nat := 4983230072969 + 3 ^ 40 * 6507031 * 2
def baseEnd_6507031 : Nat := 13749936365047061502005

theorem tailTrace_6507031 : CollatzResearch.WordTrace tailWord_6507031 prefixEnd_6507031 13749936365047061502005 := by
  unfold tailWord_6507031
  simp only [CollatzResearch.WordTrace]
  refine ⟨237330918089145474263808947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158220612059430316175872631 237330918089145474263808947)
  ·
    refine ⟨355996377133718211395713421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237330918089145474263808947 355996377133718211395713421)
    ·
      refine ⟨133498641425144329273392533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355996377133718211395713421 133498641425144329273392533)
      ·
        refine ⟨6257748816803640434690275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133498641425144329273392533 6257748816803640434690275)
        ·
          refine ⟨9386623225205460652035413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257748816803640434690275 9386623225205460652035413)
          ·
            refine ⟨13749936365047061502005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9386623225205460652035413 13749936365047061502005)
            ·
              rfl

theorem cell23_6507031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 11].length) (baseStart_6507031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507031 prefixEnd_6507031 := by exact prefixLift 6507031
  have htrace : WordTrace (prefixWord ++ tailWord_6507031) baseStart_6507031 baseEnd_6507031 := by
    simpa [prefixWord, tailWord_6507031, baseEnd_6507031] using wordTrace_append hprefix tailTrace_6507031
  have hstable : (prefixWord ++ tailWord_6507031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507031).length < 2 ^ (prefixWord ++ tailWord_6507031).sum := by decide
  have hdescent : baseEnd_6507031 < baseStart_6507031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507041 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6507041 : Nat := 118140960795 + 6507041 * 2 ^ 59
def prefixEnd_6507041 : Nat := 4983230072969 + 3 ^ 40 * 6507041 * 2
def baseEnd_6507041 : Nat := 3341239671512980905862169

theorem tailTrace_6507041 : CollatzResearch.WordTrace tailWord_6507041 prefixEnd_6507041 3341239671512980905862169 := by
  unfold tailWord_6507041
  simp only [CollatzResearch.WordTrace]
  refine ⟨237331282819109245971672977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158220855212739497314448651 237331282819109245971672977)
  ·
    refine ⟨177998462114331934478754733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237331282819109245971672977 177998462114331934478754733)
    ·
      refine ⟨66749423292874475429533025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177998462114331934478754733 66749423292874475429533025)
      ·
        refine ⟨50062067469655856572149769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66749423292874475429533025 50062067469655856572149769)
        ·
          refine ⟨37546550602241892429112327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50062067469655856572149769 37546550602241892429112327)
          ·
            refine ⟨56319825903362838643668491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37546550602241892429112327 56319825903362838643668491)
            ·
              refine ⟨84479738855044257965502737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56319825903362838643668491 84479738855044257965502737)
              ·
                refine ⟨63359804141283193474127053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84479738855044257965502737 63359804141283193474127053)
                ·
                  refine ⟨23759926552981197552797645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63359804141283193474127053 23759926552981197552797645)
                  ·
                    refine ⟨8909972457367949082299117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23759926552981197552797645 8909972457367949082299117)
                    ·
                      refine ⟨3341239671512980905862169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8909972457367949082299117 3341239671512980905862169)
                      ·
                        rfl

theorem cell23_6507041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6507041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507041 prefixEnd_6507041 := by exact prefixLift 6507041
  have htrace : WordTrace (prefixWord ++ tailWord_6507041) baseStart_6507041 baseEnd_6507041 := by
    simpa [prefixWord, tailWord_6507041, baseEnd_6507041] using wordTrace_append hprefix tailTrace_6507041
  have hstable : (prefixWord ++ tailWord_6507041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507041).length < 2 ^ (prefixWord ++ tailWord_6507041).sum := by decide
  have hdescent : baseEnd_6507041 < baseStart_6507041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507048 : List Nat := [2, 1, 5, 2, 1, 3, 1, 8]
def baseStart_6507048 : Nat := 118140960795 + 6507048 * 2 ^ 59
def prefixEnd_6507048 : Nat := 4983230072969 + 3 ^ 40 * 6507048 * 2
def baseEnd_6507048 : Nat := 123749750588057865869431

theorem tailTrace_6507048 : CollatzResearch.WordTrace tailWord_6507048 prefixEnd_6507048 123749750588057865869431 := by
  unfold tailWord_6507048
  simp only [CollatzResearch.WordTrace]
  refine ⟨118665769065041943083588899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158221025420055924111451865 118665769065041943083588899)
  ·
    refine ⟨177998653597562914625383349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118665769065041943083588899 177998653597562914625383349)
    ·
      refine ⟨16687373774771523246129689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177998653597562914625383349 16687373774771523246129689)
      ·
        refine ⟨12515530331078642434597267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16687373774771523246129689 12515530331078642434597267)
        ·
          refine ⟨18773295496617963651895901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12515530331078642434597267 18773295496617963651895901)
          ·
            refine ⟨7039985811231736369460963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18773295496617963651895901 7039985811231736369460963)
            ·
              refine ⟨10559978716847604554191445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039985811231736369460963 10559978716847604554191445)
              ·
                refine ⟨123749750588057865869431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10559978716847604554191445 123749750588057865869431)
                ·
                  rfl

theorem cell23_6507048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 8].length) (baseStart_6507048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507048 prefixEnd_6507048 := by exact prefixLift 6507048
  have htrace : WordTrace (prefixWord ++ tailWord_6507048) baseStart_6507048 baseEnd_6507048 := by
    simpa [prefixWord, tailWord_6507048, baseEnd_6507048] using wordTrace_append hprefix tailTrace_6507048
  have hstable : (prefixWord ++ tailWord_6507048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507048).length < 2 ^ (prefixWord ++ tailWord_6507048).sum := by decide
  have hdescent : baseEnd_6507048 < baseStart_6507048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507076 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6507076 : Nat := 118140960795 + 6507076 * 2 ^ 59
def prefixEnd_6507076 : Nat := 4983230072969 + 3 ^ 40 * 6507076 * 2
def baseEnd_6507076 : Nat := 3341257643335888268924509

theorem tailTrace_6507076 : CollatzResearch.WordTrace tailWord_6507076 prefixEnd_6507076 3341257643335888268924509 := by
  unfold tailWord_6507076
  simp only [CollatzResearch.WordTrace]
  refine ⟨118666279686991223474598541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158221706249321631299464721 118666279686991223474598541)
  ·
    refine ⟨44499854882621708802974453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118666279686991223474598541 44499854882621708802974453)
    ·
      refine ⟨4171861395245785200278855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44499854882621708802974453 4171861395245785200278855)
      ·
        refine ⟨6257792092868677800418283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171861395245785200278855 6257792092868677800418283)
        ·
          refine ⟨9386688139303016700627425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257792092868677800418283 9386688139303016700627425)
          ·
            refine ⟨7040016104477262525470569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9386688139303016700627425 7040016104477262525470569)
            ·
              refine ⟨5280012078357946894102927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040016104477262525470569 5280012078357946894102927)
              ·
                refine ⟨7920018117536920341154391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280012078357946894102927 7920018117536920341154391)
                ·
                  refine ⟨11880027176305380511731587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7920018117536920341154391 11880027176305380511731587)
                  ·
                    refine ⟨17820040764458070767597381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11880027176305380511731587 17820040764458070767597381)
                    ·
                      refine ⟨3341257643335888268924509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17820040764458070767597381 3341257643335888268924509)
                      ·
                        rfl

theorem cell23_6507076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6507076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507076 prefixEnd_6507076 := by exact prefixLift 6507076
  have htrace : WordTrace (prefixWord ++ tailWord_6507076) baseStart_6507076 baseEnd_6507076 := by
    simpa [prefixWord, tailWord_6507076, baseEnd_6507076] using wordTrace_append hprefix tailTrace_6507076
  have hstable : (prefixWord ++ tailWord_6507076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507076).length < 2 ^ (prefixWord ++ tailWord_6507076).sum := by decide
  have hdescent : baseEnd_6507076 < baseStart_6507076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507092 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_6507092 : Nat := 118140960795 + 6507092 * 2 ^ 59
def prefixEnd_6507092 : Nat := 4983230072969 + 3 ^ 40 * 6507092 * 2
def baseEnd_6507092 : Nat := 3341265859026360206324435

theorem tailTrace_6507092 : CollatzResearch.WordTrace tailWord_6507092 prefixEnd_6507092 3341265859026360206324435 := by
  unfold tailWord_6507092
  simp only [CollatzResearch.WordTrace]
  refine ⟨118666571470962240840889765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158222095294616321121186353 118666571470962240840889765)
  ·
    refine ⟨22249982150805420157666831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118666571470962240840889765 22249982150805420157666831)
    ·
      refine ⟨33374973226208130236500247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22249982150805420157666831 33374973226208130236500247)
      ·
        refine ⟨50062459839312195354750371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33374973226208130236500247 50062459839312195354750371)
        ·
          refine ⟨75093689758968293032125557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50062459839312195354750371 75093689758968293032125557)
          ·
            refine ⟨7040033414903277471761771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75093689758968293032125557 7040033414903277471761771)
            ·
              refine ⟨10560050122354916207642657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040033414903277471761771 10560050122354916207642657)
              ·
                refine ⟨7920037591766187155731993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560050122354916207642657 7920037591766187155731993)
                ·
                  refine ⟨5940028193824640366798995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920037591766187155731993 5940028193824640366798995)
                  ·
                    refine ⟨8910042290736960550198493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5940028193824640366798995 8910042290736960550198493)
                    ·
                      refine ⟨3341265859026360206324435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8910042290736960550198493 3341265859026360206324435)
                      ·
                        rfl

theorem cell23_6507092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_6507092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507092 prefixEnd_6507092 := by exact prefixLift 6507092
  have htrace : WordTrace (prefixWord ++ tailWord_6507092) baseStart_6507092 baseEnd_6507092 := by
    simpa [prefixWord, tailWord_6507092, baseEnd_6507092] using wordTrace_append hprefix tailTrace_6507092
  have hstable : (prefixWord ++ tailWord_6507092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507092).length < 2 ^ (prefixWord ++ tailWord_6507092).sum := by decide
  have hdescent : baseEnd_6507092 < baseStart_6507092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507131 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3]
def baseStart_6507131 : Nat := 118140960795 + 6507131 * 2 ^ 59
def prefixEnd_6507131 : Nat := 4983230072969 + 3 ^ 40 * 6507131 * 2
def baseEnd_6507131 : Nat := 3341285884771885553736755

theorem tailTrace_6507131 : CollatzResearch.WordTrace tailWord_6507131 prefixEnd_6507131 3341285884771885553736755 := by
  unfold tailWord_6507131
  simp only [CollatzResearch.WordTrace]
  refine ⟨237334565388783191342449247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158223043592522127561632831 237334565388783191342449247)
  ·
    refine ⟨356001848083174787013673871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237334565388783191342449247 356001848083174787013673871)
    ·
      refine ⟨534002772124762180520510807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356001848083174787013673871 534002772124762180520510807)
      ·
        refine ⟨801004158187143270780766211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534002772124762180520510807 801004158187143270780766211)
        ·
          refine ⟨1201506237280714906171149317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801004158187143270780766211 1201506237280714906171149317)
          ·
            refine ⟨225282419490134044907090497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1201506237280714906171149317 225282419490134044907090497)
            ·
              refine ⟨168961814617600533680317873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225282419490134044907090497 168961814617600533680317873)
              ·
                refine ⟨126721360963200400260238405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168961814617600533680317873 126721360963200400260238405)
                ·
                  refine ⟨23760255180600075048794701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126721360963200400260238405 23760255180600075048794701)
                  ·
                    refine ⟨8910095692725028143298013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23760255180600075048794701 8910095692725028143298013)
                    ·
                      refine ⟨3341285884771885553736755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8910095692725028143298013 3341285884771885553736755)
                      ·
                        rfl

theorem cell23_6507131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3].length) (baseStart_6507131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507131 prefixEnd_6507131 := by exact prefixLift 6507131
  have htrace : WordTrace (prefixWord ++ tailWord_6507131) baseStart_6507131 baseEnd_6507131 := by
    simpa [prefixWord, tailWord_6507131, baseEnd_6507131] using wordTrace_append hprefix tailTrace_6507131
  have hstable : (prefixWord ++ tailWord_6507131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507131).length < 2 ^ (prefixWord ++ tailWord_6507131).sum := by decide
  have hdescent : baseEnd_6507131 < baseStart_6507131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507151 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 2, 5]
def baseStart_6507151 : Nat := 118140960795 + 6507151 * 2 ^ 59
def prefixEnd_6507151 : Nat := 4983230072969 + 3 ^ 40 * 6507151 * 2
def baseEnd_6507151 : Nat := 1113765384794991825162221

theorem tailTrace_6507151 : CollatzResearch.WordTrace tailWord_6507151 prefixEnd_6507151 1113765384794991825162221 := by
  unfold tailWord_6507151
  simp only [CollatzResearch.WordTrace]
  refine ⟨237335294848710734758177307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158223529899140489838784871 237335294848710734758177307)
  ·
    refine ⟨356002942273066102137265961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237335294848710734758177307 356002942273066102137265961)
    ·
      refine ⟨267002206704799576602949471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356002942273066102137265961 267002206704799576602949471)
      ·
        refine ⟨400503310057199364904424207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267002206704799576602949471 400503310057199364904424207)
        ·
          refine ⟨600754965085799047356636311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400503310057199364904424207 600754965085799047356636311)
          ·
            refine ⟨901132447628698571034954467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600754965085799047356636311 901132447628698571034954467)
            ·
              refine ⟨1351698671443047856552431701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901132447628698571034954467 1351698671443047856552431701)
              ·
                refine ⟨15840218805973217068973809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1351698671443047856552431701 15840218805973217068973809)
                ·
                  refine ⟨11880164104479912801730357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15840218805973217068973809 11880164104479912801730357)
                  ·
                    refine ⟨1113765384794991825162221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11880164104479912801730357 1113765384794991825162221)
                    ·
                      rfl

theorem cell23_6507151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_6507151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507151 prefixEnd_6507151 := by exact prefixLift 6507151
  have htrace : WordTrace (prefixWord ++ tailWord_6507151) baseStart_6507151 baseEnd_6507151 := by
    simpa [prefixWord, tailWord_6507151, baseEnd_6507151] using wordTrace_append hprefix tailTrace_6507151
  have hstable : (prefixWord ++ tailWord_6507151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507151).length < 2 ^ (prefixWord ++ tailWord_6507151).sum := by decide
  have hdescent : baseEnd_6507151 < baseStart_6507151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507161 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_6507161 : Nat := 118140960795 + 6507161 * 2 ^ 59
def prefixEnd_6507161 : Nat := 4983230072969 + 3 ^ 40 * 6507161 * 2
def baseEnd_6507161 : Nat := 3341301289191520436361617

theorem tailTrace_6507161 : CollatzResearch.WordTrace tailWord_6507161 prefixEnd_6507161 3341301289191520436361617 := by
  unfold tailWord_6507161
  simp only [CollatzResearch.WordTrace]
  refine ⟨237335659578674506466041337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158223773052449670977360891 237335659578674506466041337)
  ·
    refine ⟨178001744684005879849531003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237335659578674506466041337 178001744684005879849531003)
    ·
      refine ⟨267002617026008819774296505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178001744684005879849531003 267002617026008819774296505)
      ·
        refine ⟨200251962769506614830722379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267002617026008819774296505 200251962769506614830722379)
        ·
          refine ⟨300377944154259922246083569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200251962769506614830722379 300377944154259922246083569)
          ·
            refine ⟨225283458115694941684562677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300377944154259922246083569 225283458115694941684562677)
            ·
              refine ⟨21120324198346400782927751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225283458115694941684562677 21120324198346400782927751)
              ·
                refine ⟨31680486297519601174391627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21120324198346400782927751 31680486297519601174391627)
                ·
                  refine ⟨47520729446279401761587441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31680486297519601174391627 47520729446279401761587441)
                  ·
                    refine ⟨35640547084709551321190581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47520729446279401761587441 35640547084709551321190581)
                    ·
                      refine ⟨3341301289191520436361617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35640547084709551321190581 3341301289191520436361617)
                      ·
                        rfl

theorem cell23_6507161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_6507161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507161 prefixEnd_6507161 := by exact prefixLift 6507161
  have htrace : WordTrace (prefixWord ++ tailWord_6507161) baseStart_6507161 baseEnd_6507161 := by
    simpa [prefixWord, tailWord_6507161, baseEnd_6507161] using wordTrace_append hprefix tailTrace_6507161
  have hstable : (prefixWord ++ tailWord_6507161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507161).length < 2 ^ (prefixWord ++ tailWord_6507161).sum := by decide
  have hdescent : baseEnd_6507161 < baseStart_6507161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507171 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_6507171 : Nat := 118140960795 + 6507171 * 2 ^ 59
def prefixEnd_6507171 : Nat := 4983230072969 + 3 ^ 40 * 6507171 * 2
def baseEnd_6507171 : Nat := 3341306423998065397236571

theorem tailTrace_6507171 : CollatzResearch.WordTrace tailWord_6507171 prefixEnd_6507171 3341306423998065397236571 := by
  unfold tailWord_6507171
  simp only [CollatzResearch.WordTrace]
  refine ⟨237336024308638278173905367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158224016205758852115936911 237336024308638278173905367)
  ·
    refine ⟨356004036462957417260858051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237336024308638278173905367 356004036462957417260858051)
    ·
      refine ⟨534006054694436125891287077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356004036462957417260858051 534006054694436125891287077)
      ·
        refine ⟨100126135255206773604616327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534006054694436125891287077 100126135255206773604616327)
        ·
          refine ⟨150189202882810160406924491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100126135255206773604616327 150189202882810160406924491)
          ·
            refine ⟨225283804324215240610386737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150189202882810160406924491 225283804324215240610386737)
            ·
              refine ⟨168962853243161430457790053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225283804324215240610386737 168962853243161430457790053)
              ·
                refine ⟨31680534983092768210835635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168962853243161430457790053 31680534983092768210835635)
                ·
                  refine ⟨47520802474639152316253453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31680534983092768210835635 47520802474639152316253453)
                  ·
                    refine ⟨17820300927989682118595045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47520802474639152316253453 17820300927989682118595045)
                    ·
                      refine ⟨3341306423998065397236571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17820300927989682118595045 3341306423998065397236571)
                      ·
                        rfl

theorem cell23_6507171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_6507171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507171 prefixEnd_6507171 := by exact prefixLift 6507171
  have htrace : WordTrace (prefixWord ++ tailWord_6507171) baseStart_6507171 baseEnd_6507171 := by
    simpa [prefixWord, tailWord_6507171, baseEnd_6507171] using wordTrace_append hprefix tailTrace_6507171
  have hstable : (prefixWord ++ tailWord_6507171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507171).length < 2 ^ (prefixWord ++ tailWord_6507171).sum := by decide
  have hdescent : baseEnd_6507171 < baseStart_6507171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507251 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_6507251 : Nat := 118140960795 + 6507251 * 2 ^ 59
def prefixEnd_6507251 : Nat := 4983230072969 + 3 ^ 40 * 6507251 * 2
def baseEnd_6507251 : Nat := 3341347502450425084236203

theorem tailTrace_6507251 : CollatzResearch.WordTrace tailWord_6507251 prefixEnd_6507251 3341347502450425084236203 := by
  unfold tailWord_6507251
  simp only [CollatzResearch.WordTrace]
  refine ⟨237338942148348451836817607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158225961432232301224545071 237338942148348451836817607)
  ·
    refine ⟨356008413222522677755226411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237338942148348451836817607 356008413222522677755226411)
    ·
      refine ⟨534012619833784016632839617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356008413222522677755226411 534012619833784016632839617)
      ·
        refine ⟨400509464875338012474629713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534012619833784016632839617 400509464875338012474629713)
        ·
          refine ⟨300382098656503509355972285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400509464875338012474629713 300382098656503509355972285)
          ·
            refine ⟨112643286996188816008489607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300382098656503509355972285 112643286996188816008489607)
            ·
              refine ⟨168964930494283224012734411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112643286996188816008489607 168964930494283224012734411)
              ·
                refine ⟨253447395741424836019101617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168964930494283224012734411 253447395741424836019101617)
                ·
                  refine ⟨190085546806068627014326213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253447395741424836019101617 190085546806068627014326213)
                  ·
                    refine ⟨35641040026137867565186165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190085546806068627014326213 35641040026137867565186165)
                    ·
                      refine ⟨3341347502450425084236203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35641040026137867565186165 3341347502450425084236203)
                      ·
                        rfl

theorem cell23_6507251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_6507251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507251 prefixEnd_6507251 := by exact prefixLift 6507251
  have htrace : WordTrace (prefixWord ++ tailWord_6507251) baseStart_6507251 baseEnd_6507251 := by
    simpa [prefixWord, tailWord_6507251, baseEnd_6507251] using wordTrace_append hprefix tailTrace_6507251
  have hstable : (prefixWord ++ tailWord_6507251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507251).length < 2 ^ (prefixWord ++ tailWord_6507251).sum := by decide
  have hdescent : baseEnd_6507251 < baseStart_6507251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507262 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_6507262 : Nat := 118140960795 + 6507262 * 2 ^ 59
def prefixEnd_6507262 : Nat := 4983230072969 + 3 ^ 40 * 6507262 * 2
def baseEnd_6507262 : Nat := 371261461193069393466517

theorem tailTrace_6507262 : CollatzResearch.WordTrace tailWord_6507262 prefixEnd_6507262 371261461193069393466517 := by
  unfold tailWord_6507262
  simp only [CollatzResearch.WordTrace]
  refine ⟨29667417918913575089433505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158226228900872400476978693 29667417918913575089433505)
  ·
    refine ⟨22250563439185181317075129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29667417918913575089433505 22250563439185181317075129)
    ·
      refine ⟨16687922579388885987806347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22250563439185181317075129 16687922579388885987806347)
      ·
        refine ⟨25031883869083328981709521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16687922579388885987806347 25031883869083328981709521)
        ·
          refine ⟨18773912901812496736282141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25031883869083328981709521 18773912901812496736282141)
          ·
            refine ⟨7040217338179686276105803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18773912901812496736282141 7040217338179686276105803)
            ·
              refine ⟨10560326007269529414158705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040217338179686276105803 10560326007269529414158705)
              ·
                refine ⟨7920244505452147060619029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560326007269529414158705 7920244505452147060619029)
                ·
                  refine ⟨371261461193069393466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7920244505452147060619029 371261461193069393466517)
                  ·
                    rfl

theorem cell23_6507262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_6507262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507262 prefixEnd_6507262 := by exact prefixLift 6507262
  have htrace : WordTrace (prefixWord ++ tailWord_6507262) baseStart_6507262 baseEnd_6507262 := by
    simpa [prefixWord, tailWord_6507262, baseEnd_6507262] using wordTrace_append hprefix tailTrace_6507262
  have hstable : (prefixWord ++ tailWord_6507262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507262).length < 2 ^ (prefixWord ++ tailWord_6507262).sum := by decide
  have hdescent : baseEnd_6507262 < baseStart_6507262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507265 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_6507265 : Nat := 118140960795 + 6507265 * 2 ^ 59
def prefixEnd_6507265 : Nat := 4983230072969 + 3 ^ 40 * 6507265 * 2
def baseEnd_6507265 : Nat := 3341354691179588029461139

theorem tailTrace_6507265 : CollatzResearch.WordTrace tailWord_6507265 prefixEnd_6507265 3341354691179588029461139 := by
  unfold tailWord_6507265
  simp only [CollatzResearch.WordTrace]
  refine ⟨237339452770297732227827249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158226301846865154818551499 237339452770297732227827249)
  ·
    refine ⟨178004589577723299170870437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237339452770297732227827249 178004589577723299170870437)
    ·
      refine ⟨33375860545823118594538207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178004589577723299170870437 33375860545823118594538207)
      ·
        refine ⟨50063790818734677891807311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33375860545823118594538207 50063790818734677891807311)
        ·
          refine ⟨75095686228102016837710967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50063790818734677891807311 75095686228102016837710967)
          ·
            refine ⟨112643529342153025256566451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75095686228102016837710967 112643529342153025256566451)
            ·
              refine ⟨168965294013229537884849677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112643529342153025256566451 168965294013229537884849677)
              ·
                refine ⟨63361985254961076706818629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168965294013229537884849677 63361985254961076706818629)
                ·
                  refine ⟨11880372235305201882528493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63361985254961076706818629 11880372235305201882528493)
                  ·
                    refine ⟨4455139588239450705948185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11880372235305201882528493 4455139588239450705948185)
                    ·
                      refine ⟨3341354691179588029461139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455139588239450705948185 3341354691179588029461139)
                      ·
                        rfl

theorem cell23_6507265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_6507265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507265 prefixEnd_6507265 := by exact prefixLift 6507265
  have htrace : WordTrace (prefixWord ++ tailWord_6507265) baseStart_6507265 baseEnd_6507265 := by
    simpa [prefixWord, tailWord_6507265, baseEnd_6507265] using wordTrace_append hprefix tailTrace_6507265
  have hstable : (prefixWord ++ tailWord_6507265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507265).length < 2 ^ (prefixWord ++ tailWord_6507265).sum := by decide
  have hdescent : baseEnd_6507265 < baseStart_6507265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
