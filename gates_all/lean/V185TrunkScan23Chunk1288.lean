import V185TrunkScan23Chunk1287

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7628343 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 2, 5]
def baseStart_7628343 : Nat := 118140960795 + 7628343 * 2 ^ 59
def prefixEnd_7628343 : Nat := 4983230072969 + 3 ^ 40 * 7628343 * 2
def baseEnd_7628343 : Nat := 1305668852120250935543465

theorem tailTrace_7628343 : CollatzResearch.WordTrace tailWord_7628343 prefixEnd_7628343 1305668852120250935543465 := by
  unfold tailWord_7628343
  simp only [CollatzResearch.WordTrace]
  refine ⟨278228526602823603106929683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185485684401882402071286455 278228526602823603106929683)
  ·
    refine ⟨417342789904235404660394525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278228526602823603106929683 417342789904235404660394525)
    ·
      refine ⟨156503546214088276747647947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417342789904235404660394525 156503546214088276747647947)
      ·
        refine ⟨234755319321132415121471921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156503546214088276747647947 234755319321132415121471921)
        ·
          refine ⟨176066489490849311341103941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234755319321132415121471921 176066489490849311341103941)
          ·
            refine ⟨33012466779534245876456989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176066489490849311341103941 33012466779534245876456989)
            ·
              refine ⟨12379675042325342203671371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33012466779534245876456989 12379675042325342203671371)
              ·
                refine ⟨18569512563488013305507057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12379675042325342203671371 18569512563488013305507057)
                ·
                  refine ⟨13927134422616009979130293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18569512563488013305507057 13927134422616009979130293)
                  ·
                    refine ⟨1305668852120250935543465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13927134422616009979130293 1305668852120250935543465)
                    ·
                      rfl

theorem cell23_7628343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_7628343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628343 prefixEnd_7628343 := by exact prefixLift 7628343
  have htrace : WordTrace (prefixWord ++ tailWord_7628343) baseStart_7628343 baseEnd_7628343 := by
    simpa [prefixWord, tailWord_7628343, baseEnd_7628343] using wordTrace_append hprefix tailTrace_7628343
  have hstable : (prefixWord ++ tailWord_7628343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628343).length < 2 ^ (prefixWord ++ tailWord_7628343).sum := by decide
  have hdescent : baseEnd_7628343 < baseStart_7628343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628358 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7628358 : Nat := 118140960795 + 7628358 * 2 ^ 59
def prefixEnd_7628358 : Nat := 4983230072969 + 3 ^ 40 * 7628358 * 2
def baseEnd_7628358 : Nat := 3917014258570570247942827

theorem tailTrace_7628358 : CollatzResearch.WordTrace tailWord_7628358 prefixEnd_7628358 3917014258570570247942827 := by
  unfold tailWord_7628358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694658553055289395897679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185486049131846173779150485 8694658553055289395897679)
  ·
    refine ⟨13041987829582934093846519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694658553055289395897679 13041987829582934093846519)
    ·
      refine ⟨19562981744374401140769779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041987829582934093846519 19562981744374401140769779)
      ·
        refine ⟨29344472616561601711154669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562981744374401140769779 29344472616561601711154669)
        ·
          refine ⟨11004177231210600641683001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29344472616561601711154669 11004177231210600641683001)
          ·
            refine ⟨8253132923407950481262251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11004177231210600641683001 8253132923407950481262251)
            ·
              refine ⟨12379699385111925721893377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253132923407950481262251 12379699385111925721893377)
              ·
                refine ⟨9284774538833944291420033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12379699385111925721893377 9284774538833944291420033)
                ·
                  refine ⟨6963580904125458218565025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9284774538833944291420033 6963580904125458218565025)
                  ·
                    refine ⟨5222685678094093663923769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963580904125458218565025 5222685678094093663923769)
                    ·
                      refine ⟨3917014258570570247942827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222685678094093663923769 3917014258570570247942827)
                      ·
                        rfl

theorem cell23_7628358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7628358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628358 prefixEnd_7628358 := by exact prefixLift 7628358
  have htrace : WordTrace (prefixWord ++ tailWord_7628358) baseStart_7628358 baseEnd_7628358 := by
    simpa [prefixWord, tailWord_7628358, baseEnd_7628358] using wordTrace_append hprefix tailTrace_7628358
  have hstable : (prefixWord ++ tailWord_7628358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628358).length < 2 ^ (prefixWord ++ tailWord_7628358).sum := by decide
  have hdescent : baseEnd_7628358 < baseStart_7628358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628376 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_7628376 : Nat := 118140960795 + 7628376 * 2 ^ 59
def prefixEnd_7628376 : Nat := 4983230072969 + 3 ^ 40 * 7628376 * 2
def baseEnd_7628376 : Nat := 3917023501222351177517743

theorem tailTrace_7628376 : CollatzResearch.WordTrace tailWord_7628376 prefixEnd_7628376 3917023501222351177517743 := by
  unfold tailWord_7628376
  simp only [CollatzResearch.WordTrace]
  refine ⟨139114865105852024871440491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185486486807802699828587321 139114865105852024871440491)
  ·
    refine ⟨208672297658778037307160737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139114865105852024871440491 208672297658778037307160737)
    ·
      refine ⟨156504223244083527980370553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208672297658778037307160737 156504223244083527980370553)
      ·
        refine ⟨117378167433062645985277915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156504223244083527980370553 117378167433062645985277915)
        ·
          refine ⟨176067251149593968977916873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117378167433062645985277915 176067251149593968977916873)
          ·
            refine ⟨132050438362195476733437655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176067251149593968977916873 132050438362195476733437655)
            ·
              refine ⟨198075657543293215100156483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132050438362195476733437655 198075657543293215100156483)
              ·
                refine ⟨297113486314939822650234725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198075657543293215100156483 297113486314939822650234725)
                ·
                  refine ⟨55708778684051216746919011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297113486314939822650234725 55708778684051216746919011)
                  ·
                    refine ⟨83563168026076825120378517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55708778684051216746919011 83563168026076825120378517)
                    ·
                      refine ⟨3917023501222351177517743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83563168026076825120378517 3917023501222351177517743)
                      ·
                        rfl

theorem cell23_7628376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_7628376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628376 prefixEnd_7628376 := by exact prefixLift 7628376
  have htrace : WordTrace (prefixWord ++ tailWord_7628376) baseStart_7628376 baseEnd_7628376 := by
    simpa [prefixWord, tailWord_7628376, baseEnd_7628376] using wordTrace_append hprefix tailTrace_7628376
  have hstable : (prefixWord ++ tailWord_7628376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628376).length < 2 ^ (prefixWord ++ tailWord_7628376).sum := by decide
  have hdescent : baseEnd_7628376 < baseStart_7628376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628424 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_7628424 : Nat := 118140960795 + 7628424 * 2 ^ 59
def prefixEnd_7628424 : Nat := 4983230072969 + 3 ^ 40 * 7628424 * 2
def baseEnd_7628424 : Nat := 1305682716097922329905841

theorem tailTrace_7628424 : CollatzResearch.WordTrace tailWord_7628424 prefixEnd_7628424 1305682716097922329905841 := by
  unfold tailWord_7628424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139115740457765076970314163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185487653943686769293752217 139115740457765076970314163)
  ·
    refine ⟨208673610686647615455471245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139115740457765076970314163 208673610686647615455471245)
    ·
      refine ⟨78252604007492855795801717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208673610686647615455471245 78252604007492855795801717)
      ·
        refine ⟨7336181625702455230856411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78252604007492855795801717 7336181625702455230856411)
        ·
          refine ⟨11004272438553682846284617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336181625702455230856411 11004272438553682846284617)
          ·
            refine ⟨8253204328915262134713463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11004272438553682846284617 8253204328915262134713463)
            ·
              refine ⟨12379806493372893202070195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253204328915262134713463 12379806493372893202070195)
              ·
                refine ⟨18569709740059339803105293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12379806493372893202070195 18569709740059339803105293)
                ·
                  refine ⟨6963641152522252426164485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18569709740059339803105293 6963641152522252426164485)
                  ·
                    refine ⟨1305682716097922329905841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6963641152522252426164485 1305682716097922329905841)
                    ·
                      rfl

theorem cell23_7628424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_7628424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628424 prefixEnd_7628424 := by exact prefixLift 7628424
  have htrace : WordTrace (prefixWord ++ tailWord_7628424) baseStart_7628424 baseEnd_7628424 := by
    simpa [prefixWord, tailWord_7628424, baseEnd_7628424] using wordTrace_append hprefix tailTrace_7628424
  have hstable : (prefixWord ++ tailWord_7628424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628424).length < 2 ^ (prefixWord ++ tailWord_7628424).sum := by decide
  have hdescent : baseEnd_7628424 < baseStart_7628424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628463 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 1, 6]
def baseStart_7628463 : Nat := 118140960795 + 7628463 * 2 ^ 59
def prefixEnd_7628463 : Nat := 4983230072969 + 3 ^ 40 * 7628463 * 2
def baseEnd_7628463 : Nat := 1305689391346430779043281

theorem tailTrace_7628463 : CollatzResearch.WordTrace tailWord_7628463 prefixEnd_7628463 1305689391346430779043281 := by
  unfold tailWord_7628463
  simp only [CollatzResearch.WordTrace]
  refine ⟨278232903362388863601298043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185488602241592575734198695 278232903362388863601298043)
  ·
    refine ⟨417349355043583295401947065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278232903362388863601298043 417349355043583295401947065)
    ·
      refine ⟨313012016282687471551460299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417349355043583295401947065 313012016282687471551460299)
      ·
        refine ⟨469518024424031207327190449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313012016282687471551460299 469518024424031207327190449)
        ·
          refine ⟨352138518318023405495392837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469518024424031207327190449 352138518318023405495392837)
          ·
            refine ⟨66025972184629388530386157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352138518318023405495392837 66025972184629388530386157)
            ·
              refine ⟨24759739569236020698894809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66025972184629388530386157 24759739569236020698894809)
              ·
                refine ⟨18569804676927015524171107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24759739569236020698894809 18569804676927015524171107)
                ·
                  refine ⟨27854707015390523286256661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18569804676927015524171107 27854707015390523286256661)
                  ·
                    refine ⟨1305689391346430779043281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27854707015390523286256661 1305689391346430779043281)
                    ·
                      rfl

theorem cell23_7628463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_7628463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628463 prefixEnd_7628463 := by exact prefixLift 7628463
  have htrace : WordTrace (prefixWord ++ tailWord_7628463) baseStart_7628463 baseEnd_7628463 := by
    simpa [prefixWord, tailWord_7628463, baseEnd_7628463] using wordTrace_append hprefix tailTrace_7628463
  have hstable : (prefixWord ++ tailWord_7628463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628463).length < 2 ^ (prefixWord ++ tailWord_7628463).sum := by decide
  have hdescent : baseEnd_7628463 < baseStart_7628463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628487 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_7628487 : Nat := 118140960795 + 7628487 * 2 ^ 59
def prefixEnd_7628487 : Nat := 4983230072969 + 3 ^ 40 * 7628487 * 2
def baseEnd_7628487 : Nat := 3917080497575000243229733

theorem tailTrace_7628487 : CollatzResearch.WordTrace tailWord_7628487 prefixEnd_7628487 3917080497575000243229733 := by
  unfold tailWord_7628487
  simp only [CollatzResearch.WordTrace]
  refine ⟨278233778714301915700171715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185489185809534610466781143 278233778714301915700171715)
  ·
    refine ⟨417350668071452873550257573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278233778714301915700171715 417350668071452873550257573)
    ·
      refine ⟨78253250263397413790673295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417350668071452873550257573 78253250263397413790673295)
      ·
        refine ⟨117379875395096120686009943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78253250263397413790673295 117379875395096120686009943)
        ·
          refine ⟨176069813092644181029014915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117379875395096120686009943 176069813092644181029014915)
          ·
            refine ⟨264104719638966271543522373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176069813092644181029014915 264104719638966271543522373)
            ·
              refine ⟨49519634932306175914410445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264104719638966271543522373 49519634932306175914410445)
              ·
                refine ⟨18569863099614815967903917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49519634932306175914410445 18569863099614815967903917)
                ·
                  refine ⟨6963698662355555987963969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18569863099614815967903917 6963698662355555987963969)
                  ·
                    refine ⟨5222773996766666990972977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963698662355555987963969 5222773996766666990972977)
                    ·
                      refine ⟨3917080497575000243229733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222773996766666990972977 3917080497575000243229733)
                      ·
                        rfl

theorem cell23_7628487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_7628487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628487 prefixEnd_7628487 := by exact prefixLift 7628487
  have htrace : WordTrace (prefixWord ++ tailWord_7628487) baseStart_7628487 baseEnd_7628487 := by
    simpa [prefixWord, tailWord_7628487, baseEnd_7628487] using wordTrace_append hprefix tailTrace_7628487
  have hstable : (prefixWord ++ tailWord_7628487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628487).length < 2 ^ (prefixWord ++ tailWord_7628487).sum := by decide
  have hdescent : baseEnd_7628487 < baseStart_7628487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628508 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7628508 : Nat := 118140960795 + 7628508 * 2 ^ 59
def prefixEnd_7628508 : Nat := 4983230072969 + 3 ^ 40 * 7628508 * 2
def baseEnd_7628508 : Nat := 3917091280668744661067137

theorem tailTrace_7628508 : CollatzResearch.WordTrace tailWord_7628508 prefixEnd_7628508 3917091280668744661067137 := by
  unfold tailWord_7628508
  simp only [CollatzResearch.WordTrace]
  refine ⟨139117272323612918143343089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185489696431483890857790785 139117272323612918143343089)
  ·
    refine ⟨104337954242709688607507317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139117272323612918143343089 104337954242709688607507317)
    ·
      refine ⟨9781683210254033306953811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104337954242709688607507317 9781683210254033306953811)
      ·
        refine ⟨14672524815381049960430717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781683210254033306953811 14672524815381049960430717)
        ·
          refine ⟨5502196805767893735161519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14672524815381049960430717 5502196805767893735161519)
          ·
            refine ⟨8253295208651840602742279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502196805767893735161519 8253295208651840602742279)
            ·
              refine ⟨12379942812977760904113419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253295208651840602742279 12379942812977760904113419)
              ·
                refine ⟨18569914219466641356170129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12379942812977760904113419 18569914219466641356170129)
                ·
                  refine ⟨13927435664599981017127597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18569914219466641356170129 13927435664599981017127597)
                  ·
                    refine ⟨5222788374224992881422849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13927435664599981017127597 5222788374224992881422849)
                    ·
                      refine ⟨3917091280668744661067137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222788374224992881422849 3917091280668744661067137)
                      ·
                        rfl

theorem cell23_7628508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7628508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628508 prefixEnd_7628508 := by exact prefixLift 7628508
  have htrace : WordTrace (prefixWord ++ tailWord_7628508) baseStart_7628508 baseEnd_7628508 := by
    simpa [prefixWord, tailWord_7628508, baseEnd_7628508] using wordTrace_append hprefix tailTrace_7628508
  have hstable : (prefixWord ++ tailWord_7628508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628508).length < 2 ^ (prefixWord ++ tailWord_7628508).sum := by decide
  have hdescent : baseEnd_7628508 < baseStart_7628508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628543 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_7628543 : Nat := 118140960795 + 7628543 * 2 ^ 59
def prefixEnd_7628543 : Nat := 4983230072969 + 3 ^ 40 * 7628543 * 2
def baseEnd_7628543 : Nat := 3917109252491652024129475

theorem tailTrace_7628543 : CollatzResearch.WordTrace tailWord_7628543 prefixEnd_7628543 3917109252491652024129475 := by
  unfold tailWord_7628543
  simp only [CollatzResearch.WordTrace]
  refine ⟨278235821202099037264210283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185490547468066024842806855 278235821202099037264210283)
  ·
    refine ⟨417353731803148555896315425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278235821202099037264210283 417353731803148555896315425)
    ·
      refine ⟨313015298852361416922236569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417353731803148555896315425 313015298852361416922236569)
      ·
        refine ⟨234761474139271062691677427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313015298852361416922236569 234761474139271062691677427)
        ·
          refine ⟨352142211208906594037516141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234761474139271062691677427 352142211208906594037516141)
          ·
            refine ⟨132053329203339972764068553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352142211208906594037516141 132053329203339972764068553)
            ·
              refine ⟨99039996902504979573051415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132053329203339972764068553 99039996902504979573051415)
              ·
                refine ⟨148559995353757469359577123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99039996902504979573051415 148559995353757469359577123)
                ·
                  refine ⟨222839993030636204039365685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148559995353757469359577123 222839993030636204039365685)
                  ·
                    refine ⟨20891249346622144128690533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222839993030636204039365685 20891249346622144128690533)
                    ·
                      refine ⟨3917109252491652024129475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20891249346622144128690533 3917109252491652024129475)
                      ·
                        rfl

theorem cell23_7628543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_7628543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628543 prefixEnd_7628543 := by exact prefixLift 7628543
  have htrace : WordTrace (prefixWord ++ tailWord_7628543) baseStart_7628543 baseEnd_7628543 := by
    simpa [prefixWord, tailWord_7628543, baseEnd_7628543] using wordTrace_append hprefix tailTrace_7628543
  have hstable : (prefixWord ++ tailWord_7628543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628543).length < 2 ^ (prefixWord ++ tailWord_7628543).sum := by decide
  have hdescent : baseEnd_7628543 < baseStart_7628543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628580 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7628580 : Nat := 118140960795 + 7628580 * 2 ^ 59
def prefixEnd_7628580 : Nat := 4983230072969 + 3 ^ 40 * 7628580 * 2
def baseEnd_7628580 : Nat := 3917128251275868379366805

theorem tailTrace_7628580 : CollatzResearch.WordTrace tailWord_7628580 prefixEnd_7628580 3917128251275868379366805 := by
  unfold tailWord_7628580
  simp only [CollatzResearch.WordTrace]
  refine ⟨139118585351482496291653597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185491447135309995055538129 139118585351482496291653597)
  ·
    refine ⟨52169469506805936109370099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139118585351482496291653597 52169469506805936109370099)
    ·
      refine ⟨78254204260208904164055149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52169469506805936109370099 78254204260208904164055149)
      ·
        refine ⟨29345326597578339061520681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78254204260208904164055149 29345326597578339061520681)
        ·
          refine ⟨22008994948183754296140511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29345326597578339061520681 22008994948183754296140511)
          ·
            refine ⟨33013492422275631444210767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22008994948183754296140511 33013492422275631444210767)
            ·
              refine ⟨49520238633413447166316151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33013492422275631444210767 49520238633413447166316151)
              ·
                refine ⟨74280357950120170749474227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49520238633413447166316151 74280357950120170749474227)
                ·
                  refine ⟨111420536925180256124211341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74280357950120170749474227 111420536925180256124211341)
                  ·
                    refine ⟨41782701346942596046579253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111420536925180256124211341 41782701346942596046579253)
                    ·
                      refine ⟨3917128251275868379366805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41782701346942596046579253 3917128251275868379366805)
                      ·
                        rfl

theorem cell23_7628580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7628580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628580 prefixEnd_7628580 := by exact prefixLift 7628580
  have htrace : WordTrace (prefixWord ++ tailWord_7628580) baseStart_7628580 baseEnd_7628580 := by
    simpa [prefixWord, tailWord_7628580, baseEnd_7628580] using wordTrace_append hprefix tailTrace_7628580
  have hstable : (prefixWord ++ tailWord_7628580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628580).length < 2 ^ (prefixWord ++ tailWord_7628580).sum := by decide
  have hdescent : baseEnd_7628580 < baseStart_7628580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628594 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2]
def baseStart_7628594 : Nat := 118140960795 + 7628594 * 2 ^ 59
def prefixEnd_7628594 : Nat := 4983230072969 + 3 ^ 40 * 7628594 * 2
def baseEnd_7628594 : Nat := 3917135440005031324591741

theorem tailTrace_7628594 : CollatzResearch.WordTrace tailWord_7628594 prefixEnd_7628594 3917135440005031324591741 := by
  unfold tailWord_7628594
  simp only [CollatzResearch.WordTrace]
  refine ⟨69559420331228568243579209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185491787549942848649544557 69559420331228568243579209)
  ·
    refine ⟨52169565248421426182684407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69559420331228568243579209 52169565248421426182684407)
    ·
      refine ⟨78254347872632139274026611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52169565248421426182684407 78254347872632139274026611)
      ·
        refine ⟨117381521808948208911039917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78254347872632139274026611 117381521808948208911039917)
        ·
          refine ⟨44018070678355578341639969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117381521808948208911039917 44018070678355578341639969)
          ·
            refine ⟨33013553008766683756229977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44018070678355578341639969 33013553008766683756229977)
            ·
              refine ⟨24760164756575012817172483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33013553008766683756229977 24760164756575012817172483)
              ·
                refine ⟨37140247134862519225758725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24760164756575012817172483 37140247134862519225758725)
                ·
                  refine ⟨6963796337786722354829761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37140247134862519225758725 6963796337786722354829761)
                  ·
                    refine ⟨5222847253340041766122321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963796337786722354829761 5222847253340041766122321)
                    ·
                      refine ⟨3917135440005031324591741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222847253340041766122321 3917135440005031324591741)
                      ·
                        rfl

theorem cell23_7628594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_7628594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628594 prefixEnd_7628594 := by exact prefixLift 7628594
  have htrace : WordTrace (prefixWord ++ tailWord_7628594) baseStart_7628594 baseEnd_7628594 := by
    simpa [prefixWord, tailWord_7628594, baseEnd_7628594] using wordTrace_append hprefix tailTrace_7628594
  have hstable : (prefixWord ++ tailWord_7628594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628594).length < 2 ^ (prefixWord ++ tailWord_7628594).sum := by decide
  have hdescent : baseEnd_7628594 < baseStart_7628594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628600 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 7]
def baseStart_7628600 : Nat := 118140960795 + 7628600 * 2 ^ 59
def prefixEnd_7628600 : Nat := 4983230072969 + 3 ^ 40 * 7628600 * 2
def baseEnd_7628600 : Nat := 435237613432106477901857

theorem tailTrace_7628600 : CollatzResearch.WordTrace tailWord_7628600 prefixEnd_7628600 435237613432106477901857 := by
  unfold tailWord_7628600
  simp only [CollatzResearch.WordTrace]
  refine ⟨139118950081446267999517627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185491933441928357332690169 139118950081446267999517627)
  ·
    refine ⟨208678425122169401999276441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139118950081446267999517627 208678425122169401999276441)
    ·
      refine ⟨156508818841627051499457331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208678425122169401999276441 156508818841627051499457331)
      ·
        refine ⟨234763228262440577249185997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156508818841627051499457331 234763228262440577249185997)
        ·
          refine ⟨88036210598415216468444749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234763228262440577249185997 88036210598415216468444749)
          ·
            refine ⟨33013578974405706175666781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88036210598415216468444749 33013578974405706175666781)
            ·
              refine ⟨12380092115402139815875043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33013578974405706175666781 12380092115402139815875043)
              ·
                refine ⟨18570138173103209723812565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12380092115402139815875043 18570138173103209723812565)
                ·
                  refine ⟨435237613432106477901857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18570138173103209723812565 435237613432106477901857)
                  ·
                    rfl

theorem cell23_7628600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_7628600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628600 prefixEnd_7628600 := by exact prefixLift 7628600
  have htrace : WordTrace (prefixWord ++ tailWord_7628600) baseStart_7628600 baseEnd_7628600 := by
    simpa [prefixWord, tailWord_7628600, baseEnd_7628600] using wordTrace_append hprefix tailTrace_7628600
  have hstable : (prefixWord ++ tailWord_7628600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628600).length < 2 ^ (prefixWord ++ tailWord_7628600).sum := by decide
  have hdescent : baseEnd_7628600 < baseStart_7628600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628611 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 2, 2, 2]
def baseStart_7628611 : Nat := 118140960795 + 7628611 * 2 ^ 59
def prefixEnd_7628611 : Nat := 4983230072969 + 3 ^ 40 * 7628611 * 2
def baseEnd_7628611 : Nat := 3917144169176157758079163

theorem tailTrace_7628611 : CollatzResearch.WordTrace tailWord_7628611 prefixEnd_7628611 3917144169176157758079163 := by
  unfold tailWord_7628611
  simp only [CollatzResearch.WordTrace]
  refine ⟨278238301365852684877685687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185492200910568456585123791 278238301365852684877685687)
  ·
    refine ⟨417357452048779027316528531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278238301365852684877685687 417357452048779027316528531)
    ·
      refine ⟨626036178073168540974792797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417357452048779027316528531 626036178073168540974792797)
      ·
        refine ⟨234763566777438202865547299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626036178073168540974792797 234763566777438202865547299)
        ·
          refine ⟨352145350166157304298320949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234763566777438202865547299 352145350166157304298320949)
          ·
            refine ⟨33013626578077247277967589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352145350166157304298320949 33013626578077247277967589)
            ·
              refine ⟨6190054983389483864618923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33013626578077247277967589 6190054983389483864618923)
              ·
                refine ⟨9285082475084225796928385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190054983389483864618923 9285082475084225796928385)
                ·
                  refine ⟨6963811856313169347696289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9285082475084225796928385 6963811856313169347696289)
                  ·
                    refine ⟨5222858892234877010772217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963811856313169347696289 5222858892234877010772217)
                    ·
                      refine ⟨3917144169176157758079163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222858892234877010772217 3917144169176157758079163)
                      ·
                        rfl

theorem cell23_7628611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_7628611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628611 prefixEnd_7628611 := by exact prefixLift 7628611
  have htrace : WordTrace (prefixWord ++ tailWord_7628611) baseStart_7628611 baseEnd_7628611 := by
    simpa [prefixWord, tailWord_7628611, baseEnd_7628611] using wordTrace_append hprefix tailTrace_7628611
  have hstable : (prefixWord ++ tailWord_7628611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628611).length < 2 ^ (prefixWord ++ tailWord_7628611).sum := by decide
  have hdescent : baseEnd_7628611 < baseStart_7628611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628614 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7628614 : Nat := 118140960795 + 7628614 * 2 ^ 59
def prefixEnd_7628614 : Nat := 4983230072969 + 3 ^ 40 * 7628614 * 2
def baseEnd_7628614 : Nat := 3917145709618121246341649

theorem tailTrace_7628614 : CollatzResearch.WordTrace tailWord_7628614 prefixEnd_7628614 3917145709618121246341649 := by
  unfold tailWord_7628614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694950337026306762188903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185492273856561210926696597 8694950337026306762188903)
  ·
    refine ⟨13042425505539460143283355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694950337026306762188903 13042425505539460143283355)
    ·
      refine ⟨19563638258309190214925033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13042425505539460143283355 19563638258309190214925033)
      ·
        refine ⟨14672728693731892661193775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19563638258309190214925033 14672728693731892661193775)
        ·
          refine ⟨22009093040597838991790663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14672728693731892661193775 22009093040597838991790663)
          ·
            refine ⟨33013639560896758487685995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22009093040597838991790663 33013639560896758487685995)
            ·
              refine ⟨49520459341345137731528993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33013639560896758487685995 49520459341345137731528993)
              ·
                refine ⟨37140344506008853298646745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49520459341345137731528993 37140344506008853298646745)
                ·
                  refine ⟨27855258379506639973985059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37140344506008853298646745 27855258379506639973985059)
                  ·
                    refine ⟨41782887569259959960977589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27855258379506639973985059 41782887569259959960977589)
                    ·
                      refine ⟨3917145709618121246341649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41782887569259959960977589 3917145709618121246341649)
                      ·
                        rfl

theorem cell23_7628614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7628614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628614 prefixEnd_7628614 := by exact prefixLift 7628614
  have htrace : WordTrace (prefixWord ++ tailWord_7628614) baseStart_7628614 baseEnd_7628614 := by
    simpa [prefixWord, tailWord_7628614, baseEnd_7628614] using wordTrace_append hprefix tailTrace_7628614
  have hstable : (prefixWord ++ tailWord_7628614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628614).length < 2 ^ (prefixWord ++ tailWord_7628614).sum := by decide
  have hdescent : baseEnd_7628614 < baseStart_7628614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628640 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_7628640 : Nat := 118140960795 + 7628640 * 2 ^ 59
def prefixEnd_7628640 : Nat := 4983230072969 + 3 ^ 40 * 7628640 * 2
def baseEnd_7628640 : Nat := 3917159060115138144616529

theorem tailTrace_7628640 : CollatzResearch.WordTrace tailWord_7628640 prefixEnd_7628640 3917159060115138144616529 := by
  unfold tailWord_7628640
  simp only [CollatzResearch.WordTrace]
  refine ⟨139119679541373811415245687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185492906055165081886994249 139119679541373811415245687)
  ·
    refine ⟨208679519312060717122868531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139119679541373811415245687 208679519312060717122868531)
    ·
      refine ⟨313019278968091075684302797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208679519312060717122868531 313019278968091075684302797)
      ·
        refine ⟨117382229613034153381613549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313019278968091075684302797 117382229613034153381613549)
        ·
          refine ⟨44018336104887807518105081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117382229613034153381613549 44018336104887807518105081)
          ·
            refine ⟨33013752078665855638578811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44018336104887807518105081 33013752078665855638578811)
            ·
              refine ⟨49520628117998783457868217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33013752078665855638578811 49520628117998783457868217)
              ·
                refine ⟨37140471088499087593401163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49520628117998783457868217 37140471088499087593401163)
                ·
                  refine ⟨55710706632748631390101745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37140471088499087593401163 55710706632748631390101745)
                  ·
                    refine ⟨41783029974561473542576309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55710706632748631390101745 41783029974561473542576309)
                    ·
                      refine ⟨3917159060115138144616529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41783029974561473542576309 3917159060115138144616529)
                      ·
                        rfl

theorem cell23_7628640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_7628640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628640 prefixEnd_7628640 := by exact prefixLift 7628640
  have htrace : WordTrace (prefixWord ++ tailWord_7628640) baseStart_7628640 baseEnd_7628640 := by
    simpa [prefixWord, tailWord_7628640, baseEnd_7628640] using wordTrace_append hprefix tailTrace_7628640
  have hstable : (prefixWord ++ tailWord_7628640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628640).length < 2 ^ (prefixWord ++ tailWord_7628640).sum := by decide
  have hdescent : baseEnd_7628640 < baseStart_7628640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628654 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7628654 : Nat := 118140960795 + 7628654 * 2 ^ 59
def prefixEnd_7628654 : Nat := 4983230072969 + 3 ^ 40 * 7628654 * 2
def baseEnd_7628654 : Nat := 3917166248844301089841465

theorem tailTrace_7628654 : CollatzResearch.WordTrace tailWord_7628654 prefixEnd_7628654 3917166248844301089841465 := by
  unfold tailWord_7628654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34779983713087112902687627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185493246469797935481000677 34779983713087112902687627)
  ·
    refine ⟨52169975569630669354031441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34779983713087112902687627 52169975569630669354031441)
    ·
      refine ⟨39127481677223002015523581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52169975569630669354031441 39127481677223002015523581)
      ·
        refine ⟨14672805628958625755821343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39127481677223002015523581 14672805628958625755821343)
        ·
          refine ⟨22009208443437938633732015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14672805628958625755821343 22009208443437938633732015)
          ·
            refine ⟨33013812665156907950598023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22009208443437938633732015 33013812665156907950598023)
            ·
              refine ⟨49520718997735361925897035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33013812665156907950598023 49520718997735361925897035)
              ·
                refine ⟨74281078496603042888845553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49520718997735361925897035 74281078496603042888845553)
                ·
                  refine ⟨55710808872452282166634165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74281078496603042888845553 55710808872452282166634165)
                  ·
                    refine ⟨5222888331792401453121953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55710808872452282166634165 5222888331792401453121953)
                    ·
                      refine ⟨3917166248844301089841465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222888331792401453121953 3917166248844301089841465)
                      ·
                        rfl

theorem cell23_7628654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7628654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628654 prefixEnd_7628654 := by exact prefixLift 7628654
  have htrace : WordTrace (prefixWord ++ tailWord_7628654) baseStart_7628654 baseEnd_7628654 := by
    simpa [prefixWord, tailWord_7628654, baseEnd_7628654] using wordTrace_append hprefix tailTrace_7628654
  have hstable : (prefixWord ++ tailWord_7628654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628654).length < 2 ^ (prefixWord ++ tailWord_7628654).sum := by decide
  have hdescent : baseEnd_7628654 < baseStart_7628654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628677 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_7628677 : Nat := 118140960795 + 7628677 * 2 ^ 59
def prefixEnd_7628677 : Nat := 4983230072969 + 3 ^ 40 * 7628677 * 2
def baseEnd_7628677 : Nat := 1305726019633118166617953

theorem tailTrace_7628677 : CollatzResearch.WordTrace tailWord_7628677 prefixEnd_7628677 1305726019633118166617953 := by
  unfold tailWord_7628677
  simp only [CollatzResearch.WordTrace]
  refine ⟨278240708583613578149588285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185493805722409052099725523 278240708583613578149588285)
  ·
    refine ⟨104340265718855091806095607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278240708583613578149588285 104340265718855091806095607)
    ·
      refine ⟨156510398578282637709143411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104340265718855091806095607 156510398578282637709143411)
      ·
        refine ⟨234765597867423956563715117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156510398578282637709143411 234765597867423956563715117)
        ·
          refine ⟨88037099200283983711393169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234765597867423956563715117 88037099200283983711393169)
          ·
            refine ⟨66027824400212987783544877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88037099200283983711393169 66027824400212987783544877)
            ·
              refine ⟨24760434150079870418829329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66027824400212987783544877 24760434150079870418829329)
              ·
                refine ⟨18570325612559902814121997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24760434150079870418829329 18570325612559902814121997)
                ·
                  refine ⟨6963872104709963555295749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18570325612559902814121997 6963872104709963555295749)
                  ·
                    refine ⟨1305726019633118166617953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6963872104709963555295749 1305726019633118166617953)
                    ·
                      rfl

theorem cell23_7628677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_7628677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628677 prefixEnd_7628677 := by exact prefixLift 7628677
  have htrace : WordTrace (prefixWord ++ tailWord_7628677) baseStart_7628677 baseEnd_7628677 := by
    simpa [prefixWord, tailWord_7628677, baseEnd_7628677] using wordTrace_append hprefix tailTrace_7628677
  have hstable : (prefixWord ++ tailWord_7628677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628677).length < 2 ^ (prefixWord ++ tailWord_7628677).sum := by decide
  have hdescent : baseEnd_7628677 < baseStart_7628677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628711 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7628711 : Nat := 118140960795 + 7628711 * 2 ^ 59
def prefixEnd_7628711 : Nat := 4983230072969 + 3 ^ 40 * 7628711 * 2
def baseEnd_7628711 : Nat := 1305731839080535788942901

theorem tailTrace_7628711 : CollatzResearch.WordTrace tailWord_7628711 prefixEnd_7628711 1305731839080535788942901 := by
  unfold tailWord_7628711
  simp only [CollatzResearch.WordTrace]
  refine ⟨278241948665490401956325987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185494632443660267970883991 278241948665490401956325987)
  ·
    refine ⟨417362922998235602934488981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278241948665490401956325987 417362922998235602934488981)
    ·
      refine ⟨19563887015542293887554171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 417362922998235602934488981 19563887015542293887554171)
      ·
        refine ⟨29345830523313440831331257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563887015542293887554171 29345830523313440831331257)
        ·
          refine ⟨22009372892485080623498443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29345830523313440831331257 22009372892485080623498443)
          ·
            refine ⟨33014059338727620935247665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22009372892485080623498443 33014059338727620935247665)
            ·
              refine ⟨24760544504045715701435749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33014059338727620935247665 24760544504045715701435749)
              ·
                refine ⟨4642602094508571694019203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24760544504045715701435749 4642602094508571694019203)
                ·
                  refine ⟨6963903141762857541028805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642602094508571694019203 6963903141762857541028805)
                  ·
                    refine ⟨1305731839080535788942901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6963903141762857541028805 1305731839080535788942901)
                    ·
                      rfl

theorem cell23_7628711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7628711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628711 prefixEnd_7628711 := by exact prefixLift 7628711
  have htrace : WordTrace (prefixWord ++ tailWord_7628711) baseStart_7628711 baseEnd_7628711 := by
    simpa [prefixWord, tailWord_7628711, baseEnd_7628711] using wordTrace_append hprefix tailTrace_7628711
  have hstable : (prefixWord ++ tailWord_7628711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628711).length < 2 ^ (prefixWord ++ tailWord_7628711).sum := by decide
  have hdescent : baseEnd_7628711 < baseStart_7628711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628744 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_7628744 : Nat := 118140960795 + 7628744 * 2 ^ 59
def prefixEnd_7628744 : Nat := 4983230072969 + 3 ^ 40 * 7628744 * 2
def baseEnd_7628744 : Nat := 3917212462103205737716051

theorem tailTrace_7628744 : CollatzResearch.WordTrace tailWord_7628744 prefixEnd_7628744 3917212462103205737716051 := by
  unfold tailWord_7628744
  simp only [CollatzResearch.WordTrace]
  refine ⟨139121576137185424296138643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185495434849580565728184857 139121576137185424296138643)
  ·
    refine ⟨208682364205778136444207965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139121576137185424296138643 208682364205778136444207965)
    ·
      refine ⟨78255886577166801166577987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208682364205778136444207965 78255886577166801166577987)
      ·
        refine ⟨117383829865750201749866981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78255886577166801166577987 117383829865750201749866981)
        ·
          refine ⟨22009468099828162828100059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117383829865750201749866981 22009468099828162828100059)
          ·
            refine ⟨33014202149742244242150089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22009468099828162828100059 33014202149742244242150089)
            ·
              refine ⟨24760651612306683181612567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33014202149742244242150089 24760651612306683181612567)
              ·
                refine ⟨37140977418460024772418851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24760651612306683181612567 37140977418460024772418851)
                ·
                  refine ⟨55711466127690037158628277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37140977418460024772418851 55711466127690037158628277)
                  ·
                    refine ⟨5222949949470940983621401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55711466127690037158628277 5222949949470940983621401)
                    ·
                      refine ⟨3917212462103205737716051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222949949470940983621401 3917212462103205737716051)
                      ·
                        rfl

theorem cell23_7628744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_7628744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628744 prefixEnd_7628744 := by exact prefixLift 7628744
  have htrace : WordTrace (prefixWord ++ tailWord_7628744) baseStart_7628744 baseEnd_7628744 := by
    simpa [prefixWord, tailWord_7628744, baseEnd_7628744] using wordTrace_append hprefix tailTrace_7628744
  have hstable : (prefixWord ++ tailWord_7628744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628744).length < 2 ^ (prefixWord ++ tailWord_7628744).sum := by decide
  have hdescent : baseEnd_7628744 < baseStart_7628744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628761 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 2, 3, 2]
def baseStart_7628761 : Nat := 118140960795 + 7628761 * 2 ^ 59
def prefixEnd_7628761 : Nat := 4983230072969 + 3 ^ 40 * 7628761 * 2
def baseEnd_7628761 : Nat := 3917221191274332171203473

theorem tailTrace_7628761 : CollatzResearch.WordTrace tailWord_7628761 prefixEnd_7628761 3917221191274332171203473 := by
  unfold tailWord_7628761
  simp only [CollatzResearch.WordTrace]
  refine ⟨278243772315309260495646137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185495848210206173663764091 278243772315309260495646137)
  ·
    refine ⟨208682829236481945371734603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278243772315309260495646137 208682829236481945371734603)
    ·
      refine ⟨313024243854722918057601905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208682829236481945371734603 313024243854722918057601905)
      ·
        refine ⟨234768182891042188543201429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313024243854722918057601905 234768182891042188543201429)
        ·
          refine ⟨11004758573017602587962567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234768182891042188543201429 11004758573017602587962567)
          ·
            refine ⟨16507137859526403881943851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004758573017602587962567 16507137859526403881943851)
            ·
              refine ⟨24760706789289605822915777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507137859526403881943851 24760706789289605822915777)
              ·
                refine ⟨18570530091967204367186833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24760706789289605822915777 18570530091967204367186833)
                ·
                  refine ⟨13927897568975403275390125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18570530091967204367186833 13927897568975403275390125)
                  ·
                    refine ⟨5222961588365776228271297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13927897568975403275390125 5222961588365776228271297)
                    ·
                      refine ⟨3917221191274332171203473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222961588365776228271297 3917221191274332171203473)
                      ·
                        rfl

theorem cell23_7628761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_7628761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628761 prefixEnd_7628761 := by exact prefixLift 7628761
  have htrace : WordTrace (prefixWord ++ tailWord_7628761) baseStart_7628761 baseEnd_7628761 := by
    simpa [prefixWord, tailWord_7628761, baseEnd_7628761] using wordTrace_append hprefix tailTrace_7628761
  have hstable : (prefixWord ++ tailWord_7628761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628761).length < 2 ^ (prefixWord ++ tailWord_7628761).sum := by decide
  have hdescent : baseEnd_7628761 < baseStart_7628761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628808 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_7628808 : Nat := 118140960795 + 7628808 * 2 ^ 59
def prefixEnd_7628808 : Nat := 4983230072969 + 3 ^ 40 * 7628808 * 2
def baseEnd_7628808 : Nat := 3917245324865093487315757

theorem tailTrace_7628808 : CollatzResearch.WordTrace tailWord_7628808 prefixEnd_7628808 3917245324865093487315757 := by
  unfold tailWord_7628808
  simp only [CollatzResearch.WordTrace]
  refine ⟨139122743273069493761303539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185496991030759325015071385 139122743273069493761303539)
  ·
    refine ⟨208684114909604240641955309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139122743273069493761303539 208684114909604240641955309)
    ·
      refine ⟨78256543091101590240733241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208684114909604240641955309 78256543091101590240733241)
      ·
        refine ⟨58692407318326192680549931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78256543091101590240733241 58692407318326192680549931)
        ·
          refine ⟨88038610977489289020824897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58692407318326192680549931 88038610977489289020824897)
          ·
            refine ⟨66028958233116966765618673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88038610977489289020824897 66028958233116966765618673)
            ·
              refine ⟨49521718674837725074214005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66028958233116966765618673 49521718674837725074214005)
              ·
                refine ⟨4642661125766036725707563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49521718674837725074214005 4642661125766036725707563)
                ·
                  refine ⟨6963991688649055088561345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642661125766036725707563 6963991688649055088561345)
                  ·
                    refine ⟨5222993766486791316421009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6963991688649055088561345 5222993766486791316421009)
                    ·
                      refine ⟨3917245324865093487315757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5222993766486791316421009 3917245324865093487315757)
                      ·
                        rfl

theorem cell23_7628808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_7628808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628808 prefixEnd_7628808 := by exact prefixLift 7628808
  have htrace : WordTrace (prefixWord ++ tailWord_7628808) baseStart_7628808 baseEnd_7628808 := by
    simpa [prefixWord, tailWord_7628808, baseEnd_7628808] using wordTrace_append hprefix tailTrace_7628808
  have hstable : (prefixWord ++ tailWord_7628808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628808).length < 2 ^ (prefixWord ++ tailWord_7628808).sum := by decide
  have hdescent : baseEnd_7628808 < baseStart_7628808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628811 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 1, 2, 3]
def baseStart_7628811 : Nat := 118140960795 + 7628811 * 2 ^ 59
def prefixEnd_7628811 : Nat := 4983230072969 + 3 ^ 40 * 7628811 * 2
def baseEnd_7628811 : Nat := 3917246865307056975578243

theorem tailTrace_7628811 : CollatzResearch.WordTrace tailWord_7628811 prefixEnd_7628811 3917246865307056975578243 := by
  unfold tailWord_7628811
  simp only [CollatzResearch.WordTrace]
  refine ⟨278245595965128119034966287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185497063976752079356644191 278245595965128119034966287)
  ·
    refine ⟨417368393947692178552449431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278245595965128119034966287 417368393947692178552449431)
    ·
      refine ⟨626052590921538267828674147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417368393947692178552449431 626052590921538267828674147)
      ·
        refine ⟨939078886382307401743011221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626052590921538267828674147 939078886382307401743011221)
        ·
          refine ⟨44019322799170659456703651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 939078886382307401743011221 44019322799170659456703651)
          ·
            refine ⟨66028984198755989185055477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44019322799170659456703651 66028984198755989185055477)
            ·
              refine ⟨6190217268633373986098951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66028984198755989185055477 6190217268633373986098951)
              ·
                refine ⟨9285325902950060979148427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190217268633373986098951 9285325902950060979148427)
                ·
                  refine ⟨13927988854425091468722641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9285325902950060979148427 13927988854425091468722641)
                  ·
                    refine ⟨10445991640818818601541981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13927988854425091468722641 10445991640818818601541981)
                    ·
                      refine ⟨3917246865307056975578243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10445991640818818601541981 3917246865307056975578243)
                      ·
                        rfl

theorem cell23_7628811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 2, 3].length) (baseStart_7628811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628811 prefixEnd_7628811 := by exact prefixLift 7628811
  have htrace : WordTrace (prefixWord ++ tailWord_7628811) baseStart_7628811 baseEnd_7628811 := by
    simpa [prefixWord, tailWord_7628811, baseEnd_7628811] using wordTrace_append hprefix tailTrace_7628811
  have hstable : (prefixWord ++ tailWord_7628811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628811).length < 2 ^ (prefixWord ++ tailWord_7628811).sum := by decide
  have hdescent : baseEnd_7628811 < baseStart_7628811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628854 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_7628854 : Nat := 118140960795 + 7628854 * 2 ^ 59
def prefixEnd_7628854 : Nat := 4983230072969 + 3 ^ 40 * 7628854 * 2
def baseEnd_7628854 : Nat := 3917268944975200307340545

theorem tailTrace_7628854 : CollatzResearch.WordTrace tailWord_7628854 prefixEnd_7628854 3917268944975200307340545 := by
  unfold tailWord_7628854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390447768998271086173851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185498109535981558252521077 17390447768998271086173851)
  ·
    refine ⟨26085671653497406629260777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17390447768998271086173851 26085671653497406629260777)
    ·
      refine ⟨19564253740123054971945583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26085671653497406629260777 19564253740123054971945583)
      ·
        refine ⟨29346380610184582457918375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564253740123054971945583 29346380610184582457918375)
        ·
          refine ⟨44019570915276873686877563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29346380610184582457918375 44019570915276873686877563)
          ·
            refine ⟨66029356372915310530316345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44019570915276873686877563 66029356372915310530316345)
            ·
              refine ⟨49522017279686482897737259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66029356372915310530316345 49522017279686482897737259)
              ·
                refine ⟨74283025919529724346605889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49522017279686482897737259 74283025919529724346605889)
                ·
                  refine ⟨55712269439647293259954417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74283025919529724346605889 55712269439647293259954417)
                  ·
                    refine ⟨41784202079735469944965813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55712269439647293259954417 41784202079735469944965813)
                    ·
                      refine ⟨3917268944975200307340545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41784202079735469944965813 3917268944975200307340545)
                      ·
                        rfl

theorem cell23_7628854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_7628854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628854 prefixEnd_7628854 := by exact prefixLift 7628854
  have htrace : WordTrace (prefixWord ++ tailWord_7628854) baseStart_7628854 baseEnd_7628854 := by
    simpa [prefixWord, tailWord_7628854, baseEnd_7628854] using wordTrace_append hprefix tailTrace_7628854
  have hstable : (prefixWord ++ tailWord_7628854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628854).length < 2 ^ (prefixWord ++ tailWord_7628854).sum := by decide
  have hdescent : baseEnd_7628854 < baseStart_7628854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628862 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_7628862 : Nat := 118140960795 + 7628862 * 2 ^ 59
def prefixEnd_7628862 : Nat := 4983230072969 + 3 ^ 40 * 7628862 * 2
def baseEnd_7628862 : Nat := 3917273052820436276040509

theorem tailTrace_7628862 : CollatzResearch.WordTrace tailWord_7628862 prefixEnd_7628862 3917273052820436276040509 := by
  unfold tailWord_7628862
  simp only [CollatzResearch.WordTrace]
  refine ⟨34780932010992919343134105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185498304058628903163381893 34780932010992919343134105)
  ·
    refine ⟨26085699008244689507350579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34780932010992919343134105 26085699008244689507350579)
    ·
      refine ⟨39128548512367034261025869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26085699008244689507350579 39128548512367034261025869)
      ·
        refine ⟨14673205692137637847884701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39128548512367034261025869 14673205692137637847884701)
        ·
          refine ⟨5502452134551614192956763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14673205692137637847884701 5502452134551614192956763)
          ·
            refine ⟨8253678201827421289435145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502452134551614192956763 8253678201827421289435145)
            ·
              refine ⟨6190258651370565967076359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8253678201827421289435145 6190258651370565967076359)
              ·
                refine ⟨9285387977055848950614539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190258651370565967076359 9285387977055848950614539)
                ·
                  refine ⟨13928081965583773425921809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9285387977055848950614539 13928081965583773425921809)
                  ·
                    refine ⟨10446061474187830069441357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13928081965583773425921809 10446061474187830069441357)
                    ·
                      refine ⟨3917273052820436276040509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10446061474187830069441357 3917273052820436276040509)
                      ·
                        rfl

theorem cell23_7628862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_7628862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628862 prefixEnd_7628862 := by exact prefixLift 7628862
  have htrace : WordTrace (prefixWord ++ tailWord_7628862) baseStart_7628862 baseEnd_7628862 := by
    simpa [prefixWord, tailWord_7628862, baseEnd_7628862] using wordTrace_append hprefix tailTrace_7628862
  have hstable : (prefixWord ++ tailWord_7628862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628862).length < 2 ^ (prefixWord ++ tailWord_7628862).sum := by decide
  have hdescent : baseEnd_7628862 < baseStart_7628862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628867 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3]
def baseStart_7628867 : Nat := 118140960795 + 7628867 * 2 ^ 59
def prefixEnd_7628867 : Nat := 4983230072969 + 3 ^ 40 * 7628867 * 2
def baseEnd_7628867 : Nat := 3917275620223708756477985

theorem tailTrace_7628867 : CollatzResearch.WordTrace tailWord_7628867 prefixEnd_7628867 3917275620223708756477985 := by
  unfold tailWord_7628867
  simp only [CollatzResearch.WordTrace]
  refine ⟨278247638452925240599004855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185498425635283493732669903 278247638452925240599004855)
  ·
    refine ⟨417371457679387860898507283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278247638452925240599004855 417371457679387860898507283)
    ·
      refine ⟨626057186519081791347760925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417371457679387860898507283 626057186519081791347760925)
      ·
        refine ⟨234771444944655671755410347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626057186519081791347760925 234771444944655671755410347)
        ·
          refine ⟨352157167416983507633115521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234771444944655671755410347 352157167416983507633115521)
          ·
            refine ⟨264117875562737630724836641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352157167416983507633115521 264117875562737630724836641)
            ·
              refine ⟨198088406672053223043627481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264117875562737630724836641 198088406672053223043627481)
              ·
                refine ⟨148566305004039917282720611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198088406672053223043627481 148566305004039917282720611)
                ·
                  refine ⟨222849457506059875924080917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148566305004039917282720611 222849457506059875924080917)
                  ·
                    refine ⟨10446068320596556683941293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222849457506059875924080917 10446068320596556683941293)
                    ·
                      refine ⟨3917275620223708756477985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10446068320596556683941293 3917275620223708756477985)
                      ·
                        rfl

theorem cell23_7628867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_7628867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628867 prefixEnd_7628867 := by exact prefixLift 7628867
  have htrace : WordTrace (prefixWord ++ tailWord_7628867) baseStart_7628867 baseEnd_7628867 := by
    simpa [prefixWord, tailWord_7628867, baseEnd_7628867] using wordTrace_append hprefix tailTrace_7628867
  have hstable : (prefixWord ++ tailWord_7628867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628867).length < 2 ^ (prefixWord ++ tailWord_7628867).sum := by decide
  have hdescent : baseEnd_7628867 < baseStart_7628867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628887 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 7]
def baseStart_7628887 : Nat := 118140960795 + 7628887 * 2 ^ 59
def prefixEnd_7628887 : Nat := 4983230072969 + 3 ^ 40 * 7628887 * 2
def baseEnd_7628887 : Nat := 435253987759644297580877

theorem tailTrace_7628887 : CollatzResearch.WordTrace tailWord_7628887 prefixEnd_7628887 435253987759644297580877 := by
  unfold tailWord_7628887
  simp only [CollatzResearch.WordTrace]
  refine ⟨278248367912852784014732915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185498911941901856009821943 278248367912852784014732915)
  ·
    refine ⟨417372551869279176022099373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278248367912852784014732915 417372551869279176022099373)
    ·
      refine ⟨156514706950979691008287265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417372551869279176022099373 156514706950979691008287265)
      ·
        refine ⟨117386030213234768256215449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156514706950979691008287265 117386030213234768256215449)
        ·
          refine ⟨88039522659926076192161587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117386030213234768256215449 88039522659926076192161587)
          ·
            refine ⟨132059283989889114288242381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88039522659926076192161587 132059283989889114288242381)
            ·
              refine ⟨49522231496208417858090893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132059283989889114288242381 49522231496208417858090893)
              ·
                refine ⟨18570836811078156696784085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49522231496208417858090893 18570836811078156696784085)
                ·
                  refine ⟨435253987759644297580877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18570836811078156696784085 435253987759644297580877)
                  ·
                    rfl

theorem cell23_7628887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 7].length) (baseStart_7628887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628887 prefixEnd_7628887 := by exact prefixLift 7628887
  have htrace : WordTrace (prefixWord ++ tailWord_7628887) baseStart_7628887 baseEnd_7628887 := by
    simpa [prefixWord, tailWord_7628887, baseEnd_7628887] using wordTrace_append hprefix tailTrace_7628887
  have hstable : (prefixWord ++ tailWord_7628887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628887).length < 2 ^ (prefixWord ++ tailWord_7628887).sum := by decide
  have hdescent : baseEnd_7628887 < baseStart_7628887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628921 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 5]
def baseStart_7628921 : Nat := 118140960795 + 7628921 * 2 ^ 59
def prefixEnd_7628921 : Nat := 4983230072969 + 3 ^ 40 * 7628921 * 2
def baseEnd_7628921 : Nat := 435255927575450171689193

theorem tailTrace_7628921 : CollatzResearch.WordTrace tailWord_7628921 prefixEnd_7628921 435255927575450171689193 := by
  unfold tailWord_7628921
  simp only [CollatzResearch.WordTrace]
  refine ⟨278249607994729607821470617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185499738663153071880980411 278249607994729607821470617)
  ·
    refine ⟨208687205996047205866102963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278249607994729607821470617 208687205996047205866102963)
    ·
      refine ⟨313030808994070808799154445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208687205996047205866102963 313030808994070808799154445)
      ·
        refine ⟨117386553372776553299682917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313030808994070808799154445 117386553372776553299682917)
        ·
          refine ⟨22009978757395603743690547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117386553372776553299682917 22009978757395603743690547)
          ·
            refine ⟨33014968136093405615535821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22009978757395603743690547 33014968136093405615535821)
            ·
              refine ⟨12380613051035027105825933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33014968136093405615535821 12380613051035027105825933)
              ·
                refine ⟨4642729894138135164684725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12380613051035027105825933 4642729894138135164684725)
                ·
                  refine ⟨435255927575450171689193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4642729894138135164684725 435255927575450171689193)
                  ·
                    rfl

theorem cell23_7628921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 5].length) (baseStart_7628921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628921 prefixEnd_7628921 := by exact prefixLift 7628921
  have htrace : WordTrace (prefixWord ++ tailWord_7628921) baseStart_7628921 baseEnd_7628921 := by
    simpa [prefixWord, tailWord_7628921, baseEnd_7628921] using wordTrace_append hprefix tailTrace_7628921
  have hstable : (prefixWord ++ tailWord_7628921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628921).length < 2 ^ (prefixWord ++ tailWord_7628921).sum := by decide
  have hdescent : baseEnd_7628921 < baseStart_7628921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7628938 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_7628938 : Nat := 118140960795 + 7628938 * 2 ^ 59
def prefixEnd_7628938 : Nat := 4983230072969 + 3 ^ 40 * 7628938 * 2
def baseEnd_7628938 : Nat := 435256897483353108743351

theorem tailTrace_7628938 : CollatzResearch.WordTrace tailWord_7628938 prefixEnd_7628938 435256897483353108743351 := by
  unfold tailWord_7628938
  simp only [CollatzResearch.WordTrace]
  refine ⟨69562557008917004931209867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185500152023778679816559645 69562557008917004931209867)
  ·
    refine ⟨104343835513375507396814801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69562557008917004931209867 104343835513375507396814801)
    ·
      refine ⟨78257876635031630547611101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104343835513375507396814801 78257876635031630547611101)
      ·
        refine ⟨29346703738136861455354163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78257876635031630547611101 29346703738136861455354163)
        ·
          refine ⟨44020055607205292183031245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29346703738136861455354163 44020055607205292183031245)
          ·
            refine ⟨16507520852701984568636717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44020055607205292183031245 16507520852701984568636717)
            ·
              refine ⟨6190320319763244213238769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16507520852701984568636717 6190320319763244213238769)
              ·
                refine ⟨4642740239822433159929077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6190320319763244213238769 4642740239822433159929077)
                ·
                  refine ⟨435256897483353108743351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4642740239822433159929077 435256897483353108743351)
                  ·
                    rfl

theorem cell23_7628938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_7628938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7628938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7628938 prefixEnd_7628938 := by exact prefixLift 7628938
  have htrace : WordTrace (prefixWord ++ tailWord_7628938) baseStart_7628938 baseEnd_7628938 := by
    simpa [prefixWord, tailWord_7628938, baseEnd_7628938] using wordTrace_append hprefix tailTrace_7628938
  have hstable : (prefixWord ++ tailWord_7628938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7628938).length < 2 ^ (prefixWord ++ tailWord_7628938).sum := by decide
  have hdescent : baseEnd_7628938 < baseStart_7628938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7628938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629024 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_7629024 : Nat := 118140960795 + 7629024 * 2 ^ 59
def prefixEnd_7629024 : Nat := 4983230072969 + 3 ^ 40 * 7629024 * 2
def baseEnd_7629024 : Nat := 1305785412228821547404921

theorem tailTrace_7629024 : CollatzResearch.WordTrace tailWord_7629024 prefixEnd_7629024 1305785412228821547404921 := by
  unfold tailWord_7629024
  simp only [CollatzResearch.WordTrace]
  refine ⟨139126682356678228206235063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185502243142237637608313417 139126682356678228206235063)
  ·
    refine ⟨208690023535017342309352595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139126682356678228206235063 208690023535017342309352595)
    ·
      refine ⟨313035035302526013464028893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208690023535017342309352595 313035035302526013464028893)
      ·
        refine ⟨117388138238447255049010835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313035035302526013464028893 117388138238447255049010835)
        ·
          refine ⟨176082207357670882573516253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117388138238447255049010835 176082207357670882573516253)
          ·
            refine ⟨66030827759126580965068595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176082207357670882573516253 66030827759126580965068595)
            ·
              refine ⟨99046241638689871447602893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66030827759126580965068595 99046241638689871447602893)
              ·
                refine ⟨37142340614508701792851085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99046241638689871447602893 37142340614508701792851085)
                ·
                  refine ⟨13928377730440763172319157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37142340614508701792851085 13928377730440763172319157)
                  ·
                    refine ⟨1305785412228821547404921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13928377730440763172319157 1305785412228821547404921)
                    ·
                      rfl

theorem cell23_7629024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_7629024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629024 prefixEnd_7629024 := by exact prefixLift 7629024
  have htrace : WordTrace (prefixWord ++ tailWord_7629024) baseStart_7629024 baseEnd_7629024 := by
    simpa [prefixWord, tailWord_7629024, baseEnd_7629024] using wordTrace_append hprefix tailTrace_7629024
  have hstable : (prefixWord ++ tailWord_7629024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629024).length < 2 ^ (prefixWord ++ tailWord_7629024).sum := by decide
  have hdescent : baseEnd_7629024 < baseStart_7629024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629071 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 2, 4]
def baseStart_7629071 : Nat := 118140960795 + 7629071 * 2 ^ 59
def prefixEnd_7629071 : Nat := 4983230072969 + 3 ^ 40 * 7629071 * 2
def baseEnd_7629071 : Nat := 1305793456759075319442349

theorem tailTrace_7629071 : CollatzResearch.WordTrace tailWord_7629071 prefixEnd_7629071 1305793456759075319442349 := by
  unfold tailWord_7629071
  simp only [CollatzResearch.WordTrace]
  refine ⟨278255078944186183439431067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185503385962790788959620711 278255078944186183439431067)
  ·
    refine ⟨417382618416279275159146601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278255078944186183439431067 417382618416279275159146601)
    ·
      refine ⟨313036963812209456369359951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417382618416279275159146601 313036963812209456369359951)
      ·
        refine ⟨469555445718314184554039927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313036963812209456369359951 469555445718314184554039927)
        ·
          refine ⟨704333168577471276831059891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469555445718314184554039927 704333168577471276831059891)
          ·
            refine ⟨1056499752866206915246589837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704333168577471276831059891 1056499752866206915246589837)
            ·
              refine ⟨396187407324827593217471189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056499752866206915246589837 396187407324827593217471189)
              ·
                refine ⟨9285642359175646716034481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396187407324827593217471189 9285642359175646716034481)
                ·
                  refine ⟨6964231769381735037025861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9285642359175646716034481 6964231769381735037025861)
                  ·
                    refine ⟨1305793456759075319442349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6964231769381735037025861 1305793456759075319442349)
                    ·
                      rfl

theorem cell23_7629071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_7629071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629071 prefixEnd_7629071 := by exact prefixLift 7629071
  have htrace : WordTrace (prefixWord ++ tailWord_7629071) baseStart_7629071 baseEnd_7629071 := by
    simpa [prefixWord, tailWord_7629071, baseEnd_7629071] using wordTrace_append hprefix tailTrace_7629071
  have hstable : (prefixWord ++ tailWord_7629071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629071).length < 2 ^ (prefixWord ++ tailWord_7629071).sum := by decide
  have hdescent : baseEnd_7629071 < baseStart_7629071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629144 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_7629144 : Nat := 118140960795 + 7629144 * 2 ^ 59
def prefixEnd_7629144 : Nat := 4983230072969 + 3 ^ 40 * 7629144 * 2
def baseEnd_7629144 : Nat := 1305805951455001390904737

theorem tailTrace_7629144 : CollatzResearch.WordTrace tailWord_7629144 prefixEnd_7629144 1305805951455001390904737 := by
  unfold tailWord_7629144
  simp only [CollatzResearch.WordTrace]
  refine ⟨139128870736460858453419243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185505160981947811271225657 139128870736460858453419243)
  ·
    refine ⟨208693306104691287680128865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139128870736460858453419243 208693306104691287680128865)
    ·
      refine ⟨156519979578518465760096649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208693306104691287680128865 156519979578518465760096649)
      ·
        refine ⟨117389984683888849320072487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156519979578518465760096649 117389984683888849320072487)
        ·
          refine ⟨176084977025833273980108731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117389984683888849320072487 176084977025833273980108731)
          ·
            refine ⟨264127465538749910970163097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176084977025833273980108731 264127465538749910970163097)
            ·
              refine ⟨198095599154062433227622323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264127465538749910970163097 198095599154062433227622323)
              ·
                refine ⟨297143398731093649841433485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198095599154062433227622323 297143398731093649841433485)
                ·
                  refine ⟨111428774524160118690537557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297143398731093649841433485 111428774524160118690537557)
                  ·
                    refine ⟨1305805951455001390904737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111428774524160118690537557 1305805951455001390904737)
                    ·
                      rfl

theorem cell23_7629144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_7629144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629144 prefixEnd_7629144 := by exact prefixLift 7629144
  have htrace : WordTrace (prefixWord ++ tailWord_7629144) baseStart_7629144 baseEnd_7629144 := by
    simpa [prefixWord, tailWord_7629144, baseEnd_7629144] using wordTrace_append hprefix tailTrace_7629144
  have hstable : (prefixWord ++ tailWord_7629144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629144).length < 2 ^ (prefixWord ++ tailWord_7629144).sum := by decide
  have hdescent : baseEnd_7629144 < baseStart_7629144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629162 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7629162 : Nat := 118140960795 + 7629162 * 2 ^ 59
def prefixEnd_7629162 : Nat := 4983230072969 + 3 ^ 40 * 7629162 * 2
def baseEnd_7629162 : Nat := 3917427097016785102289129

theorem tailTrace_7629162 : CollatzResearch.WordTrace tailWord_7629162 prefixEnd_7629162 3917427097016785102289129 := by
  unfold tailWord_7629162
  simp only [CollatzResearch.WordTrace]
  refine ⟨69564599496714126495248435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185505598657904337320662493 69564599496714126495248435)
  ·
    refine ⟨104346899245071189742872653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69564599496714126495248435 104346899245071189742872653)
    ·
      refine ⟨39130087216901696153577245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104346899245071189742872653 39130087216901696153577245)
      ·
        refine ⟨14673782706338136057591467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39130087216901696153577245 14673782706338136057591467)
        ·
          refine ⟨22010674059507204086387201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14673782706338136057591467 22010674059507204086387201)
          ·
            refine ⟨16508005544630403064790401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22010674059507204086387201 16508005544630403064790401)
            ·
              refine ⟨12381004158472802298592801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16508005544630403064790401 12381004158472802298592801)
              ·
                refine ⟨9285753118854601723944601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12381004158472802298592801 9285753118854601723944601)
                ·
                  refine ⟨6964314839140951292958451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9285753118854601723944601 6964314839140951292958451)
                  ·
                    refine ⟨10446472258711426939437677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6964314839140951292958451 10446472258711426939437677)
                    ·
                      refine ⟨3917427097016785102289129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10446472258711426939437677 3917427097016785102289129)
                      ·
                        rfl

theorem cell23_7629162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7629162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629162 prefixEnd_7629162 := by exact prefixLift 7629162
  have htrace : WordTrace (prefixWord ++ tailWord_7629162) baseStart_7629162 baseEnd_7629162 := by
    simpa [prefixWord, tailWord_7629162, baseEnd_7629162] using wordTrace_append hprefix tailTrace_7629162
  have hstable : (prefixWord ++ tailWord_7629162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629162).length < 2 ^ (prefixWord ++ tailWord_7629162).sum := by decide
  have hdescent : baseEnd_7629162 < baseStart_7629162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629181 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_7629181 : Nat := 118140960795 + 7629181 * 2 ^ 59
def prefixEnd_7629181 : Nat := 4983230072969 + 3 ^ 40 * 7629181 * 2
def baseEnd_7629181 : Nat := 3917436853149220527951541

theorem tailTrace_7629181 : CollatzResearch.WordTrace tailWord_7629181 prefixEnd_7629181 3917436853149220527951541 := by
  unfold tailWord_7629181
  simp only [CollatzResearch.WordTrace]
  refine ⟨278259090973787672225935397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185506060649191781483956931 278259090973787672225935397)
  ·
    refine ⟨52173579557585188542362887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278259090973787672225935397 52173579557585188542362887)
    ·
      refine ⟨78260369336377782813544331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52173579557585188542362887 78260369336377782813544331)
      ·
        refine ⟨117390554004566674220316497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78260369336377782813544331 117390554004566674220316497)
        ·
          refine ⟨88042915503425005665237373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117390554004566674220316497 88042915503425005665237373)
          ·
            refine ⟨33016093313784377124464015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88042915503425005665237373 33016093313784377124464015)
            ·
              refine ⟨49524139970676565686696023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33016093313784377124464015 49524139970676565686696023)
              ·
                refine ⟨74286209956014848530044035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49524139970676565686696023 74286209956014848530044035)
                ·
                  refine ⟨111429314934022272795066053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74286209956014848530044035 111429314934022272795066053)
                  ·
                    refine ⟨20892996550129176149074885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111429314934022272795066053 20892996550129176149074885)
                    ·
                      refine ⟨3917436853149220527951541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20892996550129176149074885 3917436853149220527951541)
                      ·
                        rfl

theorem cell23_7629181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_7629181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629181 prefixEnd_7629181 := by exact prefixLift 7629181
  have htrace : WordTrace (prefixWord ++ tailWord_7629181) baseStart_7629181 baseEnd_7629181 := by
    simpa [prefixWord, tailWord_7629181, baseEnd_7629181] using wordTrace_append hprefix tailTrace_7629181
  have hstable : (prefixWord ++ tailWord_7629181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629181).length < 2 ^ (prefixWord ++ tailWord_7629181).sum := by decide
  have hdescent : baseEnd_7629181 < baseStart_7629181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629185 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_7629185 : Nat := 118140960795 + 7629185 * 2 ^ 59
def prefixEnd_7629185 : Nat := 4983230072969 + 3 ^ 40 * 7629185 * 2
def baseEnd_7629185 : Nat := 3917438907071838512301523

theorem tailTrace_7629185 : CollatzResearch.WordTrace tailWord_7629185 prefixEnd_7629185 3917438907071838512301523 := by
  unfold tailWord_7629185
  simp only [CollatzResearch.WordTrace]
  refine ⟨278259236865773180909081009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185506157910515453939387339 278259236865773180909081009)
  ·
    refine ⟨208694427649329885681810757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278259236865773180909081009 208694427649329885681810757)
    ·
      refine ⟨39130205184249353565339517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208694427649329885681810757 39130205184249353565339517)
      ·
        refine ⟨14673826944093507587002319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39130205184249353565339517 14673826944093507587002319)
        ·
          refine ⟨22010740416140261380503479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14673826944093507587002319 22010740416140261380503479)
          ·
            refine ⟨33016110624210392070755219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22010740416140261380503479 33016110624210392070755219)
            ·
              refine ⟨49524165936315588106132829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33016110624210392070755219 49524165936315588106132829)
              ·
                refine ⟨18571562226118345539799811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49524165936315588106132829 18571562226118345539799811)
                ·
                  refine ⟨27857343339177518309699717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18571562226118345539799811 27857343339177518309699717)
                  ·
                    refine ⟨5223251876095784683068697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27857343339177518309699717 5223251876095784683068697)
                    ·
                      refine ⟨3917438907071838512301523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223251876095784683068697 3917438907071838512301523)
                      ·
                        rfl

theorem cell23_7629185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_7629185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629185 prefixEnd_7629185 := by exact prefixLift 7629185
  have htrace : WordTrace (prefixWord ++ tailWord_7629185) baseStart_7629185 baseEnd_7629185 := by
    simpa [prefixWord, tailWord_7629185, baseEnd_7629185] using wordTrace_append hprefix tailTrace_7629185
  have hstable : (prefixWord ++ tailWord_7629185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629185).length < 2 ^ (prefixWord ++ tailWord_7629185).sum := by decide
  have hdescent : baseEnd_7629185 < baseStart_7629185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629191 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 7]
def baseStart_7629191 : Nat := 118140960795 + 7629191 * 2 ^ 59
def prefixEnd_7629191 : Nat := 4983230072969 + 3 ^ 40 * 7629191 * 2
def baseEnd_7629191 : Nat := 435271331995085054314055

theorem tailTrace_7629191 : CollatzResearch.WordTrace tailWord_7629191 prefixEnd_7629191 435271331995085054314055 := by
  unfold tailWord_7629191
  simp only [CollatzResearch.WordTrace]
  refine ⟨278259455703751443933799427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185506303802500962622532951 278259455703751443933799427)
  ·
    refine ⟨417389183555627165900699141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278259455703751443933799427 417389183555627165900699141)
    ·
      refine ⟨78260471916680093606381089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417389183555627165900699141 78260471916680093606381089)
      ·
        refine ⟨58695353937510070204785817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78260471916680093606381089 58695353937510070204785817)
        ·
          refine ⟨44021515453132552653589363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58695353937510070204785817 44021515453132552653589363)
          ·
            refine ⟨66032273179698828980384045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44021515453132552653589363 66032273179698828980384045)
            ·
              refine ⟨24762102442387060867644017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66032273179698828980384045 24762102442387060867644017)
              ·
                refine ⟨18571576831790295650733013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24762102442387060867644017 18571576831790295650733013)
                ·
                  refine ⟨435271331995085054314055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18571576831790295650733013 435271331995085054314055)
                  ·
                    rfl

theorem cell23_7629191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 7].length) (baseStart_7629191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629191 prefixEnd_7629191 := by exact prefixLift 7629191
  have htrace : WordTrace (prefixWord ++ tailWord_7629191) baseStart_7629191 baseEnd_7629191 := by
    simpa [prefixWord, tailWord_7629191, baseEnd_7629191] using wordTrace_append hprefix tailTrace_7629191
  have hstable : (prefixWord ++ tailWord_7629191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629191).length < 2 ^ (prefixWord ++ tailWord_7629191).sum := by decide
  have hdescent : baseEnd_7629191 < baseStart_7629191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629201 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_7629201 : Nat := 118140960795 + 7629201 * 2 ^ 59
def prefixEnd_7629201 : Nat := 4983230072969 + 3 ^ 40 * 7629201 * 2
def baseEnd_7629201 : Nat := 3917447122762310449701449

theorem tailTrace_7629201 : CollatzResearch.WordTrace tailWord_7629201 prefixEnd_7629201 3917447122762310449701449 := by
  unfold tailWord_7629201
  simp only [CollatzResearch.WordTrace]
  refine ⟨278259820433715215641663457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185506546955810143761108971 278259820433715215641663457)
  ·
    refine ⟨208694865325286411731247593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278259820433715215641663457 208694865325286411731247593)
    ·
      refine ⟨156521148993964808798435695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208694865325286411731247593 156521148993964808798435695)
      ·
        refine ⟨234781723490947213197653543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156521148993964808798435695 234781723490947213197653543)
        ·
          refine ⟨352172585236420819796480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234781723490947213197653543 352172585236420819796480315)
          ·
            refine ⟨528258877854631229694720473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352172585236420819796480315 528258877854631229694720473)
            ·
              refine ⟨396194158390973422271040355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528258877854631229694720473 396194158390973422271040355)
              ·
                refine ⟨594291237586460133406560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396194158390973422271040355 594291237586460133406560533)
                ·
                  refine ⟨27857401761865318753432525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 594291237586460133406560533 27857401761865318753432525)
                  ·
                    refine ⟨10446525660699494532537197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27857401761865318753432525 10446525660699494532537197)
                    ·
                      refine ⟨3917447122762310449701449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10446525660699494532537197 3917447122762310449701449)
                      ·
                        rfl

theorem cell23_7629201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_7629201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629201 prefixEnd_7629201 := by exact prefixLift 7629201
  have htrace : WordTrace (prefixWord ++ tailWord_7629201) baseStart_7629201 baseEnd_7629201 := by
    simpa [prefixWord, tailWord_7629201, baseEnd_7629201] using wordTrace_append hprefix tailTrace_7629201
  have hstable : (prefixWord ++ tailWord_7629201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629201).length < 2 ^ (prefixWord ++ tailWord_7629201).sum := by decide
  have hdescent : baseEnd_7629201 < baseStart_7629201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629218 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_7629218 : Nat := 118140960795 + 7629218 * 2 ^ 59
def prefixEnd_7629218 : Nat := 4983230072969 + 3 ^ 40 * 7629218 * 2
def baseEnd_7629218 : Nat := 3917455851933436883188871

theorem tailTrace_7629218 : CollatzResearch.WordTrace tailWord_7629218 prefixEnd_7629218 3917455851933436883188871 := by
  unfold tailWord_7629218
  simp only [CollatzResearch.WordTrace]
  refine ⟨69565110118663406886258077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185506960316435751696688205 69565110118663406886258077)
  ·
    refine ⟨26086916294498777582346779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69565110118663406886258077 26086916294498777582346779)
    ·
      refine ⟨39130374441748166373520169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26086916294498777582346779 39130374441748166373520169)
      ·
        refine ⟨29347780831311124780140127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39130374441748166373520169 29347780831311124780140127)
        ·
          refine ⟨44021671246966687170210191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29347780831311124780140127 44021671246966687170210191)
          ·
            refine ⟨66032506870450030755315287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44021671246966687170210191 66032506870450030755315287)
            ·
              refine ⟨99048760305675046132972931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66032506870450030755315287 99048760305675046132972931)
              ·
                refine ⟨148573140458512569199459397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99048760305675046132972931 148573140458512569199459397)
                ·
                  refine ⟨27857463835971106724898637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148573140458512569199459397 27857463835971106724898637)
                  ·
                    refine ⟨10446548938489165021836989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27857463835971106724898637 10446548938489165021836989)
                    ·
                      refine ⟨3917455851933436883188871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10446548938489165021836989 3917455851933436883188871)
                      ·
                        rfl

theorem cell23_7629218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_7629218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629218 prefixEnd_7629218 := by exact prefixLift 7629218
  have htrace : WordTrace (prefixWord ++ tailWord_7629218) baseStart_7629218 baseEnd_7629218 := by
    simpa [prefixWord, tailWord_7629218, baseEnd_7629218] using wordTrace_append hprefix tailTrace_7629218
  have hstable : (prefixWord ++ tailWord_7629218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629218).length < 2 ^ (prefixWord ++ tailWord_7629218).sum := by decide
  have hdescent : baseEnd_7629218 < baseStart_7629218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629221 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_7629221 : Nat := 118140960795 + 7629221 * 2 ^ 59
def prefixEnd_7629221 : Nat := 4983230072969 + 3 ^ 40 * 7629221 * 2
def baseEnd_7629221 : Nat := 1305819130791800123817119

theorem tailTrace_7629221 : CollatzResearch.WordTrace tailWord_7629221 prefixEnd_7629221 1305819130791800123817119 := by
  unfold tailWord_7629221
  simp only [CollatzResearch.WordTrace]
  refine ⟨278260549893642759057391517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185507033262428506038261011 278260549893642759057391517)
  ·
    refine ⟨104347706210116034646521819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278260549893642759057391517 104347706210116034646521819)
    ·
      refine ⟨156521559315174051969782729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104347706210116034646521819 156521559315174051969782729)
      ·
        refine ⟨117391169486380538977337047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156521559315174051969782729 117391169486380538977337047)
        ·
          refine ⟨176086754229570808466005571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117391169486380538977337047 176086754229570808466005571)
          ·
            refine ⟨264130131344356212699008357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176086754229570808466005571 264130131344356212699008357)
            ·
              refine ⟨49524399627066789881064067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264130131344356212699008357 49524399627066789881064067)
              ·
                refine ⟨74286599440600184821596101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49524399627066789881064067 74286599440600184821596101)
                ·
                  refine ⟨13928737395112534654049269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74286599440600184821596101 13928737395112534654049269)
                  ·
                    refine ⟨1305819130791800123817119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13928737395112534654049269 1305819130791800123817119)
                    ·
                      rfl

theorem cell23_7629221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_7629221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629221 prefixEnd_7629221 := by exact prefixLift 7629221
  have htrace : WordTrace (prefixWord ++ tailWord_7629221) baseStart_7629221 baseEnd_7629221 := by
    simpa [prefixWord, tailWord_7629221, baseEnd_7629221] using wordTrace_append hprefix tailTrace_7629221
  have hstable : (prefixWord ++ tailWord_7629221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629221).length < 2 ^ (prefixWord ++ tailWord_7629221).sum := by decide
  have hdescent : baseEnd_7629221 < baseStart_7629221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629236 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7629236 : Nat := 118140960795 + 7629236 * 2 ^ 59
def prefixEnd_7629236 : Nat := 4983230072969 + 3 ^ 40 * 7629236 * 2
def baseEnd_7629236 : Nat := 3917465094585217812763789

theorem tailTrace_7629236 : CollatzResearch.WordTrace tailWord_7629236 prefixEnd_7629236 3917465094585217812763789 := by
  unfold tailWord_7629236
  simp only [CollatzResearch.WordTrace]
  refine ⟨139130548494294208309593781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185507397992392277746125041 139130548494294208309593781)
  ·
    refine ⟨13043488921340082029024417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139130548494294208309593781 13043488921340082029024417)
    ·
      refine ⟨9782616691005061521768313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043488921340082029024417 9782616691005061521768313)
      ·
        refine ⟨7336962518253796141326235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9782616691005061521768313 7336962518253796141326235)
        ·
          refine ⟨11005443777380694211989353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7336962518253796141326235 11005443777380694211989353)
          ·
            refine ⟨8254082833035520658992015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11005443777380694211989353 8254082833035520658992015)
            ·
              refine ⟨12381124249553280988488023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254082833035520658992015 12381124249553280988488023)
              ·
                refine ⟨18571686374329921482732035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12381124249553280988488023 18571686374329921482732035)
                ·
                  refine ⟨27857529561494882224098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18571686374329921482732035 27857529561494882224098053)
                  ·
                    refine ⟨5223286792780290417018385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27857529561494882224098053 5223286792780290417018385)
                    ·
                      refine ⟨3917465094585217812763789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223286792780290417018385 3917465094585217812763789)
                      ·
                        rfl

theorem cell23_7629236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7629236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629236 prefixEnd_7629236 := by exact prefixLift 7629236
  have htrace : WordTrace (prefixWord ++ tailWord_7629236) baseStart_7629236 baseEnd_7629236 := by
    simpa [prefixWord, tailWord_7629236, baseEnd_7629236] using wordTrace_append hprefix tailTrace_7629236
  have hstable : (prefixWord ++ tailWord_7629236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629236).length < 2 ^ (prefixWord ++ tailWord_7629236).sum := by decide
  have hdescent : baseEnd_7629236 < baseStart_7629236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629258 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_7629258 : Nat := 118140960795 + 7629258 * 2 ^ 59
def prefixEnd_7629258 : Nat := 4983230072969 + 3 ^ 40 * 7629258 * 2
def baseEnd_7629258 : Nat := 3917476391159616726688687

theorem tailTrace_7629258 : CollatzResearch.WordTrace tailWord_7629258 prefixEnd_7629258 3917476391159616726688687 := by
  unfold tailWord_7629258
  simp only [CollatzResearch.WordTrace]
  refine ⟨69565474848627178594122107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185507932929672476250992285 69565474848627178594122107)
  ·
    refine ⟨104348212272940767891183161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69565474848627178594122107 104348212272940767891183161)
    ·
      refine ⟨78261159204705575918387371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104348212272940767891183161 78261159204705575918387371)
      ·
        refine ⟨117391738807058363877581057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78261159204705575918387371 117391738807058363877581057)
        ·
          refine ⟨88043804105293772908185793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117391738807058363877581057 88043804105293772908185793)
          ·
            refine ⟨66032853078970329681139345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88043804105293772908185793 66032853078970329681139345)
            ·
              refine ⟨49524639809227747260854509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66032853078970329681139345 49524639809227747260854509)
              ·
                refine ⟨18571739928460405222820441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49524639809227747260854509 18571739928460405222820441)
                ·
                  refine ⟨13928804946345303917115331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18571739928460405222820441 13928804946345303917115331)
                  ·
                    refine ⟨20893207419517955875672997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13928804946345303917115331 20893207419517955875672997)
                    ·
                      refine ⟨3917476391159616726688687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20893207419517955875672997 3917476391159616726688687)
                      ·
                        rfl

theorem cell23_7629258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_7629258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629258 prefixEnd_7629258 := by exact prefixLift 7629258
  have htrace : WordTrace (prefixWord ++ tailWord_7629258) baseStart_7629258 baseEnd_7629258 := by
    simpa [prefixWord, tailWord_7629258, baseEnd_7629258] using wordTrace_append hprefix tailTrace_7629258
  have hstable : (prefixWord ++ tailWord_7629258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629258).length < 2 ^ (prefixWord ++ tailWord_7629258).sum := by decide
  have hdescent : baseEnd_7629258 < baseStart_7629258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629281 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 8]
def baseStart_7629281 : Nat := 118140960795 + 7629281 * 2 ^ 59
def prefixEnd_7629281 : Nat := 4983230072969 + 3 ^ 40 * 7629281 * 2
def baseEnd_7629281 : Nat := 435276466801630015189009

theorem tailTrace_7629281 : CollatzResearch.WordTrace tailWord_7629281 prefixEnd_7629281 435276466801630015189009 := by
  unfold tailWord_7629281
  simp only [CollatzResearch.WordTrace]
  refine ⟨278262738273425389304575697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185508492182283592869717131 278262738273425389304575697)
  ·
    refine ⟨208697053705069041978431773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278262738273425389304575697 208697053705069041978431773)
    ·
      refine ⟨78261395139400890741911915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208697053705069041978431773 78261395139400890741911915)
      ·
        refine ⟨117392092709101336112867873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78261395139400890741911915 117392092709101336112867873)
        ·
          refine ⟨88044069531826002084650905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117392092709101336112867873 88044069531826002084650905)
          ·
            refine ⟨66033052148869501563488179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88044069531826002084650905 66033052148869501563488179)
            ·
              refine ⟨99049578223304252345232269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66033052148869501563488179 99049578223304252345232269)
              ·
                refine ⟨37143591833739094629462101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99049578223304252345232269 37143591833739094629462101)
                ·
                  refine ⟨435276466801630015189009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37143591833739094629462101 435276466801630015189009)
                  ·
                    rfl

theorem cell23_7629281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_7629281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629281 prefixEnd_7629281 := by exact prefixLift 7629281
  have htrace : WordTrace (prefixWord ++ tailWord_7629281) baseStart_7629281 baseEnd_7629281 := by
    simpa [prefixWord, tailWord_7629281, baseEnd_7629281] using wordTrace_append hprefix tailTrace_7629281
  have hstable : (prefixWord ++ tailWord_7629281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629281).length < 2 ^ (prefixWord ++ tailWord_7629281).sum := by decide
  have hdescent : baseEnd_7629281 < baseStart_7629281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629282 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7629282 : Nat := 118140960795 + 7629282 * 2 ^ 59
def prefixEnd_7629282 : Nat := 4983230072969 + 3 ^ 40 * 7629282 * 2
def baseEnd_7629282 : Nat := 3917488714695324632788577

theorem tailTrace_7629282 : CollatzResearch.WordTrace tailWord_7629282 prefixEnd_7629282 3917488714695324632788577 := by
  unfold tailWord_7629282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69565693686605441618840525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185508516497614510983574733 69565693686605441618840525)
  ·
    refine ⟨26087135132477040607065197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69565693686605441618840525 26087135132477040607065197)
    ·
      refine ⟨9782675674678890227649449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26087135132477040607065197 9782675674678890227649449)
      ·
        refine ⟨7337006756009167670737087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9782675674678890227649449 7337006756009167670737087)
        ·
          refine ⟨11005510134013751506105631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337006756009167670737087 11005510134013751506105631)
          ·
            refine ⟨16508265201020627259158447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005510134013751506105631 16508265201020627259158447)
            ·
              refine ⟨24762397801530940888737671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508265201020627259158447 24762397801530940888737671)
              ·
                refine ⟨37143596702296411333106507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24762397801530940888737671 37143596702296411333106507)
                ·
                  refine ⟨55715395053444616999659761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37143596702296411333106507 55715395053444616999659761)
                  ·
                    refine ⟨41786546290083462749744821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55715395053444616999659761 41786546290083462749744821)
                    ·
                      refine ⟨3917488714695324632788577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41786546290083462749744821 3917488714695324632788577)
                      ·
                        rfl

theorem cell23_7629282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7629282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629282 prefixEnd_7629282 := by exact prefixLift 7629282
  have htrace : WordTrace (prefixWord ++ tailWord_7629282) baseStart_7629282 baseEnd_7629282 := by
    simpa [prefixWord, tailWord_7629282, baseEnd_7629282] using wordTrace_append hprefix tailTrace_7629282
  have hstable : (prefixWord ++ tailWord_7629282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629282).length < 2 ^ (prefixWord ++ tailWord_7629282).sum := by decide
  have hdescent : baseEnd_7629282 < baseStart_7629282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629321 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_7629321 : Nat := 118140960795 + 7629321 * 2 ^ 59
def prefixEnd_7629321 : Nat := 4983230072969 + 3 ^ 40 * 7629321 * 2
def baseEnd_7629321 : Nat := 3917508740440849980200897

theorem tailTrace_7629321 : CollatzResearch.WordTrace tailWord_7629321 prefixEnd_7629321 3917508740440849980200897 := by
  unfold tailWord_7629321
  simp only [CollatzResearch.WordTrace]
  refine ⟨278264197193280476136031817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185509464795520317424021211 278264197193280476136031817)
  ·
    refine ⟨208698147894960357102023863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278264197193280476136031817 208698147894960357102023863)
    ·
      refine ⟨313047221842440535653035795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208698147894960357102023863 313047221842440535653035795)
      ·
        refine ⟨469570832763660803479553693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313047221842440535653035795 469570832763660803479553693)
        ·
          refine ⟨176089062286372801304832635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469570832763660803479553693 176089062286372801304832635)
          ·
            refine ⟨264133593429559201957248953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176089062286372801304832635 264133593429559201957248953)
            ·
              refine ⟨198100195072169401467936715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264133593429559201957248953 198100195072169401467936715)
              ·
                refine ⟨297150292608254102201905073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198100195072169401467936715 297150292608254102201905073)
                ·
                  refine ⟨222862719456190576651428805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297150292608254102201905073 222862719456190576651428805)
                  ·
                    refine ⟨41786759898035733122142901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 222862719456190576651428805 41786759898035733122142901)
                    ·
                      refine ⟨3917508740440849980200897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41786759898035733122142901 3917508740440849980200897)
                      ·
                        rfl

theorem cell23_7629321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_7629321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629321 prefixEnd_7629321 := by exact prefixLift 7629321
  have htrace : WordTrace (prefixWord ++ tailWord_7629321) baseStart_7629321 baseEnd_7629321 := by
    simpa [prefixWord, tailWord_7629321, baseEnd_7629321] using wordTrace_append hprefix tailTrace_7629321
  have hstable : (prefixWord ++ tailWord_7629321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629321).length < 2 ^ (prefixWord ++ tailWord_7629321).sum := by decide
  have hdescent : baseEnd_7629321 < baseStart_7629321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629332 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 6]
def baseStart_7629332 : Nat := 118140960795 + 7629332 * 2 ^ 59
def prefixEnd_7629332 : Nat := 4983230072969 + 3 ^ 40 * 7629332 * 2
def baseEnd_7629332 : Nat := 435279376525338826351483

theorem tailTrace_7629332 : CollatzResearch.WordTrace tailWord_7629332 prefixEnd_7629332 435279376525338826351483 := by
  unfold tailWord_7629332
  simp only [CollatzResearch.WordTrace]
  refine ⟨139132299198120312507341125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185509732264160416676454833 139132299198120312507341125)
  ·
    refine ⟨26087306099647558595126461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139132299198120312507341125 26087306099647558595126461)
    ·
      refine ⟨9782739787367834473172423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26087306099647558595126461 9782739787367834473172423)
      ·
        refine ⟨14674109681051751709758635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9782739787367834473172423 14674109681051751709758635)
        ·
          refine ⟨22011164521577627564637953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14674109681051751709758635 22011164521577627564637953)
          ·
            refine ⟨16508373391183220673478465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22011164521577627564637953 16508373391183220673478465)
            ·
              refine ⟨12381280043387415505108849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16508373391183220673478465 12381280043387415505108849)
              ·
                refine ⟨9285960032540561628831637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12381280043387415505108849 9285960032540561628831637)
                ·
                  refine ⟨435279376525338826351483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9285960032540561628831637 435279376525338826351483)
                  ·
                    rfl

theorem cell23_7629332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_7629332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629332 prefixEnd_7629332 := by exact prefixLift 7629332
  have htrace : WordTrace (prefixWord ++ tailWord_7629332) baseStart_7629332 baseEnd_7629332 := by
    simpa [prefixWord, tailWord_7629332, baseEnd_7629332] using wordTrace_append hprefix tailTrace_7629332
  have hstable : (prefixWord ++ tailWord_7629332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629332).length < 2 ^ (prefixWord ++ tailWord_7629332).sum := by decide
  have hdescent : baseEnd_7629332 < baseStart_7629332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629365 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_7629365 : Nat := 118140960795 + 7629365 * 2 ^ 59
def prefixEnd_7629365 : Nat := 4983230072969 + 3 ^ 40 * 7629365 * 2
def baseEnd_7629365 : Nat := 3917531333589647808050695

theorem tailTrace_7629365 : CollatzResearch.WordTrace tailWord_7629365 prefixEnd_7629365 3917531333589647808050695 := by
  unfold tailWord_7629365
  simp only [CollatzResearch.WordTrace]
  refine ⟨278265802005121071650633549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185510534670080714433755699 278265802005121071650633549)
  ·
    refine ⟨104349675751920401868987581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278265802005121071650633549 104349675751920401868987581)
    ·
      refine ⟨39131128406970150700870343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104349675751920401868987581 39131128406970150700870343)
      ·
        refine ⟨58696692610455226051305515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39131128406970150700870343 58696692610455226051305515)
        ·
          refine ⟨88045038915682839076958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58696692610455226051305515 88045038915682839076958273)
          ·
            refine ⟨66033779186762129307718705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88045038915682839076958273 66033779186762129307718705)
            ·
              refine ⟨49525334390071596980789029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66033779186762129307718705 49525334390071596980789029)
              ·
                refine ⟨9286000198138424433897943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49525334390071596980789029 9286000198138424433897943)
                ·
                  refine ⟨13929000297207636650846915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9286000198138424433897943 13929000297207636650846915)
                  ·
                    refine ⟨20893500445811454976270373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13929000297207636650846915 20893500445811454976270373)
                    ·
                      refine ⟨3917531333589647808050695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20893500445811454976270373 3917531333589647808050695)
                      ·
                        rfl

theorem cell23_7629365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_7629365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629365 prefixEnd_7629365 := by exact prefixLift 7629365
  have htrace : WordTrace (prefixWord ++ tailWord_7629365) baseStart_7629365 baseEnd_7629365 := by
    simpa [prefixWord, tailWord_7629365, baseEnd_7629365] using wordTrace_append hprefix tailTrace_7629365
  have hstable : (prefixWord ++ tailWord_7629365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629365).length < 2 ^ (prefixWord ++ tailWord_7629365).sum := by decide
  have hdescent : baseEnd_7629365 < baseStart_7629365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629399 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 1, 2, 2]
def baseStart_7629399 : Nat := 118140960795 + 7629399 * 2 ^ 59
def prefixEnd_7629399 : Nat := 4983230072969 + 3 ^ 40 * 7629399 * 2
def baseEnd_7629399 : Nat := 3917548791931900675025539

theorem tailTrace_7629399 : CollatzResearch.WordTrace tailWord_7629399 prefixEnd_7629399 3917548791931900675025539 := by
  unfold tailWord_7629399
  simp only [CollatzResearch.WordTrace]
  refine ⟨278267042086997895457371251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185511361391331930304914167 278267042086997895457371251)
  ·
    refine ⟨417400563130496843186056877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278267042086997895457371251 417400563130496843186056877)
    ·
      refine ⟨156525211173936316194771329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417400563130496843186056877 156525211173936316194771329)
      ·
        refine ⟨117393908380452237146078497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156525211173936316194771329 117393908380452237146078497)
        ·
          refine ⟨88045431285339177859558873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117393908380452237146078497 88045431285339177859558873)
          ·
            refine ⟨66034073464004383394669155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88045431285339177859558873 66034073464004383394669155)
            ·
              refine ⟨99051110196006575092003733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66034073464004383394669155 99051110196006575092003733)
              ·
                refine ⟨4643020790437808207437675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99051110196006575092003733 4643020790437808207437675)
                ·
                  refine ⟨6964531185656712311156513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643020790437808207437675 6964531185656712311156513)
                  ·
                    refine ⟨5223398389242534233367385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6964531185656712311156513 5223398389242534233367385)
                    ·
                      refine ⟨3917548791931900675025539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223398389242534233367385 3917548791931900675025539)
                      ·
                        rfl

theorem cell23_7629399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_7629399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629399 prefixEnd_7629399 := by exact prefixLift 7629399
  have htrace : WordTrace (prefixWord ++ tailWord_7629399) baseStart_7629399 baseEnd_7629399 := by
    simpa [prefixWord, tailWord_7629399, baseEnd_7629399] using wordTrace_append hprefix tailTrace_7629399
  have hstable : (prefixWord ++ tailWord_7629399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629399).length < 2 ^ (prefixWord ++ tailWord_7629399).sum := by decide
  have hdescent : baseEnd_7629399 < baseStart_7629399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629422 : List Nat := [4, 1, 2, 2, 2, 3, 2, 7]
def baseStart_7629422 : Nat := 118140960795 + 7629422 * 2 ^ 59
def prefixEnd_7629422 : Nat := 4983230072969 + 3 ^ 40 * 7629422 * 2
def baseEnd_7629422 : Nat := 145094837110627929075479

theorem tailTrace_7629422 : CollatzResearch.WordTrace tailWord_7629422 prefixEnd_7629422 145094837110627929075479 := by
  unfold tailWord_7629422
  simp only [CollatzResearch.WordTrace]
  refine ⟨34783485120739321298182315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185511920643943046923639013 34783485120739321298182315)
  ·
    refine ⟨52175227681108981947273473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34783485120739321298182315 52175227681108981947273473)
    ·
      refine ⟨39131420760831736460455105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52175227681108981947273473 39131420760831736460455105)
      ·
        refine ⟨29348565570623802345341329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39131420760831736460455105 29348565570623802345341329)
        ·
          refine ⟨22011424177967851759005997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29348565570623802345341329 22011424177967851759005997)
          ·
            refine ⟨8254284066737944409627249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22011424177967851759005997 8254284066737944409627249)
            ·
              refine ⟨6190713050053458307220437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254284066737944409627249 6190713050053458307220437)
              ·
                refine ⟨145094837110627929075479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6190713050053458307220437 145094837110627929075479)
                ·
                  rfl

theorem cell23_7629422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_7629422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629422 prefixEnd_7629422 := by exact prefixLift 7629422
  have htrace : WordTrace (prefixWord ++ tailWord_7629422) baseStart_7629422 baseEnd_7629422 := by
    simpa [prefixWord, tailWord_7629422, baseEnd_7629422] using wordTrace_append hprefix tailTrace_7629422
  have hstable : (prefixWord ++ tailWord_7629422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629422).length < 2 ^ (prefixWord ++ tailWord_7629422).sum := by decide
  have hdescent : baseEnd_7629422 < baseStart_7629422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629455 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 3, 4, 2]
def baseStart_7629455 : Nat := 118140960795 + 7629455 * 2 ^ 59
def prefixEnd_7629455 : Nat := 4983230072969 + 3 ^ 40 * 7629455 * 2
def baseEnd_7629455 : Nat := 3917577546848552455925281

theorem tailTrace_7629455 : CollatzResearch.WordTrace tailWord_7629455 prefixEnd_7629455 3917577546848552455925281 := by
  unfold tailWord_7629455
  simp only [CollatzResearch.WordTrace]
  refine ⟨278269084574795017021409819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185512723049863344680939879 278269084574795017021409819)
  ·
    refine ⟨417403626862192525532114729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278269084574795017021409819 417403626862192525532114729)
    ·
      refine ⟨313052720146644394149086047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417403626862192525532114729 313052720146644394149086047)
      ·
        refine ⟨469579080219966591223629071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313052720146644394149086047 469579080219966591223629071)
        ·
          refine ⟨704368620329949886835443607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469579080219966591223629071 704368620329949886835443607)
          ·
            refine ⟨1056552930494924830253165411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704368620329949886835443607 1056552930494924830253165411)
            ·
              refine ⟨1584829395742387245379748117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056552930494924830253165411 1584829395742387245379748117)
              ·
                refine ⟨74288877925424402127175693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1584829395742387245379748117 74288877925424402127175693)
                ·
                  refine ⟨27858329222034150797690885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74288877925424402127175693 27858329222034150797690885)
                  ·
                    refine ⟨5223436729131403274567041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27858329222034150797690885 5223436729131403274567041)
                    ·
                      refine ⟨3917577546848552455925281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223436729131403274567041 3917577546848552455925281)
                      ·
                        rfl

theorem cell23_7629455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4, 2].length) (baseStart_7629455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629455 prefixEnd_7629455 := by exact prefixLift 7629455
  have htrace : WordTrace (prefixWord ++ tailWord_7629455) baseStart_7629455 baseEnd_7629455 := by
    simpa [prefixWord, tailWord_7629455, baseEnd_7629455] using wordTrace_append hprefix tailTrace_7629455
  have hstable : (prefixWord ++ tailWord_7629455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629455).length < 2 ^ (prefixWord ++ tailWord_7629455).sum := by decide
  have hdescent : baseEnd_7629455 < baseStart_7629455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629466 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7629466 : Nat := 118140960795 + 7629466 * 2 ^ 59
def prefixEnd_7629466 : Nat := 4983230072969 + 3 ^ 40 * 7629466 * 2
def baseEnd_7629466 : Nat := 3917583195135751912887731

theorem tailTrace_7629466 : CollatzResearch.WordTrace tailWord_7629466 prefixEnd_7629466 3917583195135751912887731 := by
  unfold tailWord_7629466
  simp only [CollatzResearch.WordTrace]
  refine ⟨69567371444438791475015063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185512990518503443933373501 69567371444438791475015063)
  ·
    refine ⟨104351057166658187212522595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69567371444438791475015063 104351057166658187212522595)
    ·
      refine ⟨156526585749987280818783893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104351057166658187212522595 156526585749987280818783893)
      ·
        refine ⟨7337183707030653788380495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156526585749987280818783893 7337183707030653788380495)
        ·
          refine ⟨11005775560545980682570743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337183707030653788380495 11005775560545980682570743)
          ·
            refine ⟨16508663340818971023856115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005775560545980682570743 16508663340818971023856115)
            ·
              refine ⟨24762995011228456535784173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508663340818971023856115 24762995011228456535784173)
              ·
                refine ⟨9286123129210671200919065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24762995011228456535784173 9286123129210671200919065)
                ·
                  refine ⟨6964592346908003400689299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9286123129210671200919065 6964592346908003400689299)
                  ·
                    refine ⟨10446888520362005101033949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6964592346908003400689299 10446888520362005101033949)
                    ·
                      refine ⟨3917583195135751912887731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10446888520362005101033949 3917583195135751912887731)
                      ·
                        rfl

theorem cell23_7629466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7629466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629466 prefixEnd_7629466 := by exact prefixLift 7629466
  have htrace : WordTrace (prefixWord ++ tailWord_7629466) baseStart_7629466 baseEnd_7629466 := by
    simpa [prefixWord, tailWord_7629466, baseEnd_7629466] using wordTrace_append hprefix tailTrace_7629466
  have hstable : (prefixWord ++ tailWord_7629466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629466).length < 2 ^ (prefixWord ++ tailWord_7629466).sum := by decide
  have hdescent : baseEnd_7629466 < baseStart_7629466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629512 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 5]
def baseStart_7629512 : Nat := 118140960795 + 7629512 * 2 ^ 59
def prefixEnd_7629512 : Nat := 4983230072969 + 3 ^ 40 * 7629512 * 2
def baseEnd_7629512 : Nat := 435289646138428748101391

theorem tailTrace_7629512 : CollatzResearch.WordTrace tailWord_7629512 prefixEnd_7629512 435289646138428748101391 := by
  unfold tailWord_7629512
  simp only [CollatzResearch.WordTrace]
  refine ⟨139135581767794257878117395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185514109023725677170823193 139135581767794257878117395)
  ·
    refine ⟨208703372651691386817176093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139135581767794257878117395 208703372651691386817176093)
    ·
      refine ⟨78263764744384270056441035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208703372651691386817176093 78263764744384270056441035)
      ·
        refine ⟨117395647116576405084661553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78263764744384270056441035 117395647116576405084661553)
        ·
          refine ⟨88046735337432303813496165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117395647116576405084661553 88046735337432303813496165)
          ·
            refine ⟨16508762875768556965030531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88046735337432303813496165 16508762875768556965030531)
            ·
              refine ⟨24763144313652835447545797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508762875768556965030531 24763144313652835447545797)
              ·
                refine ⟨4643089558809906646414837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24763144313652835447545797 4643089558809906646414837)
                ·
                  refine ⟨435289646138428748101391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643089558809906646414837 435289646138428748101391)
                  ·
                    rfl

theorem cell23_7629512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 5].length) (baseStart_7629512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629512 prefixEnd_7629512 := by exact prefixLift 7629512
  have htrace : WordTrace (prefixWord ++ tailWord_7629512) baseStart_7629512 baseEnd_7629512 := by
    simpa [prefixWord, tailWord_7629512, baseEnd_7629512] using wordTrace_append hprefix tailTrace_7629512
  have hstable : (prefixWord ++ tailWord_7629512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629512).length < 2 ^ (prefixWord ++ tailWord_7629512).sum := by decide
  have hdescent : baseEnd_7629512 < baseStart_7629512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629555 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 7, 4]
def baseStart_7629555 : Nat := 118140960795 + 7629555 * 2 ^ 59
def prefixEnd_7629555 : Nat := 4983230072969 + 3 ^ 40 * 7629555 * 2
def baseEnd_7629555 : Nat := 1305876298304667354891607

theorem tailTrace_7629555 : CollatzResearch.WordTrace tailWord_7629555 prefixEnd_7629555 1305876298304667354891607 := by
  unfold tailWord_7629555
  simp only [CollatzResearch.WordTrace]
  refine ⟨278272731874432734100050119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185515154582955156066700079 278272731874432734100050119)
  ·
    refine ⟨417409097811649101150075179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278272731874432734100050119 417409097811649101150075179)
    ·
      refine ⟨626113646717473651725112769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417409097811649101150075179 626113646717473651725112769)
      ·
        refine ⟨469585235038105238793834577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626113646717473651725112769 469585235038105238793834577)
        ·
          refine ⟨352188926278578929095375933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469585235038105238793834577 352188926278578929095375933)
          ·
            refine ⟨132070847354467098410765975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352188926278578929095375933 132070847354467098410765975)
            ·
              refine ⟨198106271031700647616148963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132070847354467098410765975 198106271031700647616148963)
              ·
                refine ⟨297159406547550971424223445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198106271031700647616148963 297159406547550971424223445)
                ·
                  refine ⟨6964673590958225892755237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297159406547550971424223445 6964673590958225892755237)
                  ·
                    refine ⟨1305876298304667354891607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6964673590958225892755237 1305876298304667354891607)
                    ·
                      rfl

theorem cell23_7629555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 4].length) (baseStart_7629555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629555 prefixEnd_7629555 := by exact prefixLift 7629555
  have htrace : WordTrace (prefixWord ++ tailWord_7629555) baseStart_7629555 baseEnd_7629555 := by
    simpa [prefixWord, tailWord_7629555, baseEnd_7629555] using wordTrace_append hprefix tailTrace_7629555
  have hstable : (prefixWord ++ tailWord_7629555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629555).length < 2 ^ (prefixWord ++ tailWord_7629555).sum := by decide
  have hdescent : baseEnd_7629555 < baseStart_7629555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629557 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7629557 : Nat := 118140960795 + 7629557 * 2 ^ 59
def prefixEnd_7629557 : Nat := 4983230072969 + 3 ^ 40 * 7629557 * 2
def baseEnd_7629557 : Nat := 3917629921875311056849813

theorem tailTrace_7629557 : CollatzResearch.WordTrace tailWord_7629557 prefixEnd_7629557 3917629921875311056849813 := by
  unfold tailWord_7629557
  simp only [CollatzResearch.WordTrace]
  refine ⟨278272804820425488441622925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185515203213616992294415283 278272804820425488441622925)
  ·
    refine ⟨104352301807659558165608597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278272804820425488441622925 104352301807659558165608597)
    ·
      refine ⟨4891514147234041789012903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104352301807659558165608597 4891514147234041789012903)
      ·
        refine ⟨7337271220851062683519355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891514147234041789012903 7337271220851062683519355)
        ·
          refine ⟨11005906831276594025279033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337271220851062683519355 11005906831276594025279033)
          ·
            refine ⟨8254430123457445518959275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11005906831276594025279033 8254430123457445518959275)
            ·
              refine ⟨12381645185186168278438913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254430123457445518959275 12381645185186168278438913)
              ·
                refine ⟨9286233888889626208829185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12381645185186168278438913 9286233888889626208829185)
                ·
                  refine ⟨6964675416667219656621889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9286233888889626208829185 6964675416667219656621889)
                  ·
                    refine ⟨5223506562500414742466417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6964675416667219656621889 5223506562500414742466417)
                    ·
                      refine ⟨3917629921875311056849813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223506562500414742466417 3917629921875311056849813)
                      ·
                        rfl

theorem cell23_7629557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7629557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629557 prefixEnd_7629557 := by exact prefixLift 7629557
  have htrace : WordTrace (prefixWord ++ tailWord_7629557) baseStart_7629557 baseEnd_7629557 := by
    simpa [prefixWord, tailWord_7629557, baseEnd_7629557] using wordTrace_append hprefix tailTrace_7629557
  have hstable : (prefixWord ++ tailWord_7629557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629557).length < 2 ^ (prefixWord ++ tailWord_7629557).sum := by decide
  have hdescent : baseEnd_7629557 < baseStart_7629557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629562 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_7629562 : Nat := 118140960795 + 7629562 * 2 ^ 59
def prefixEnd_7629562 : Nat := 4983230072969 + 3 ^ 40 * 7629562 * 2
def baseEnd_7629562 : Nat := 3917632489278583537287289

theorem tailTrace_7629562 : CollatzResearch.WordTrace tailWord_7629562 prefixEnd_7629562 3917632489278583537287289 := by
  unfold tailWord_7629562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69568246796351843573888735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185515324790271582863703293 69568246796351843573888735)
  ·
    refine ⟨104352370194527765360833103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69568246796351843573888735 104352370194527765360833103)
    ·
      refine ⟨156528555291791648041249655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104352370194527765360833103 156528555291791648041249655)
      ·
        refine ⟨234792832937687472061874483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156528555291791648041249655 234792832937687472061874483)
        ·
          refine ⟨352189249406531208092811725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234792832937687472061874483 352189249406531208092811725)
          ·
            refine ⟨132070968527449203034804397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352189249406531208092811725 132070968527449203034804397)
            ·
              refine ⟨49526613197793451138051649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132070968527449203034804397 49526613197793451138051649)
              ·
                refine ⟨37144959898345088353538737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49526613197793451138051649 37144959898345088353538737)
                ·
                  refine ⟨27858719923758816265154053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37144959898345088353538737 27858719923758816265154053)
                  ·
                    refine ⟨5223509985704778049716385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27858719923758816265154053 5223509985704778049716385)
                    ·
                      refine ⟨3917632489278583537287289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223509985704778049716385 3917632489278583537287289)
                      ·
                        rfl

theorem cell23_7629562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_7629562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629562 prefixEnd_7629562 := by exact prefixLift 7629562
  have htrace : WordTrace (prefixWord ++ tailWord_7629562) baseStart_7629562 baseEnd_7629562 := by
    simpa [prefixWord, tailWord_7629562, baseEnd_7629562] using wordTrace_append hprefix tailTrace_7629562
  have hstable : (prefixWord ++ tailWord_7629562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629562).length < 2 ^ (prefixWord ++ tailWord_7629562).sum := by decide
  have hdescent : baseEnd_7629562 < baseStart_7629562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629585 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 6]
def baseStart_7629585 : Nat := 118140960795 + 7629585 * 2 ^ 59
def prefixEnd_7629585 : Nat := 4983230072969 + 3 ^ 40 * 7629585 * 2
def baseEnd_7629585 : Nat := 435293811037070771922187

theorem tailTrace_7629585 : CollatzResearch.WordTrace tailWord_7629585 prefixEnd_7629585 435293811037070771922187 := by
  unfold tailWord_7629585
  simp only [CollatzResearch.WordTrace]
  refine ⟨278273826064324049223642209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185515884042882699482428139 278273826064324049223642209)
  ·
    refine ⟨208705369548243036917731657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278273826064324049223642209 208705369548243036917731657)
    ·
      refine ⟨156529027161182277688298743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208705369548243036917731657 156529027161182277688298743)
      ·
        refine ⟨234793540741773416532448115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156529027161182277688298743 234793540741773416532448115)
        ·
          refine ⟨352190311112660124798672173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234793540741773416532448115 352190311112660124798672173)
          ·
            refine ⟨132071366667247546799502065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352190311112660124798672173 132071366667247546799502065)
            ·
              refine ⟨99053525000435660099626549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132071366667247546799502065 99053525000435660099626549)
              ·
                refine ⟨9286267968790843134339989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99053525000435660099626549 9286267968790843134339989)
                ·
                  refine ⟨435293811037070771922187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9286267968790843134339989 435293811037070771922187)
                  ·
                    rfl

theorem cell23_7629585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_7629585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629585 prefixEnd_7629585 := by exact prefixLift 7629585
  have htrace : WordTrace (prefixWord ++ tailWord_7629585) baseStart_7629585 baseEnd_7629585 := by
    simpa [prefixWord, tailWord_7629585, baseEnd_7629585] using wordTrace_append hprefix tailTrace_7629585
  have hstable : (prefixWord ++ tailWord_7629585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629585).length < 2 ^ (prefixWord ++ tailWord_7629585).sum := by decide
  have hdescent : baseEnd_7629585 < baseStart_7629585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629636 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 6]
def baseStart_7629636 : Nat := 118140960795 + 7629636 * 2 ^ 59
def prefixEnd_7629636 : Nat := 4983230072969 + 3 ^ 40 * 7629636 * 2
def baseEnd_7629636 : Nat := 435296720760779583084661

theorem tailTrace_7629636 : CollatzResearch.WordTrace tailWord_7629636 prefixEnd_7629636 435296720760779583084661 := by
  unfold tailWord_7629636
  simp only [CollatzResearch.WordTrace]
  refine ⟨139137843093569642466874381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185517124124759523289165841 139137843093569642466874381)
  ·
    refine ⟨52176691160088615925077893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139137843093569642466874381 52176691160088615925077893)
    ·
      refine ⟨9783129592516615485952105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52176691160088615925077893 9783129592516615485952105)
      ·
        refine ⟨7337347194387461614464079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9783129592516615485952105 7337347194387461614464079)
        ·
          refine ⟨11006020791581192421696119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337347194387461614464079 11006020791581192421696119)
          ·
            refine ⟨16509031187371788632544179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006020791581192421696119 16509031187371788632544179)
            ·
              refine ⟨24763546781057682948816269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16509031187371788632544179 24763546781057682948816269)
              ·
                refine ⟨9286330042896631105806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24763546781057682948816269 9286330042896631105806101)
                ·
                  refine ⟨435296720760779583084661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9286330042896631105806101 435296720760779583084661)
                  ·
                    rfl

theorem cell23_7629636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_7629636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629636 prefixEnd_7629636 := by exact prefixLift 7629636
  have htrace : WordTrace (prefixWord ++ tailWord_7629636) baseStart_7629636 baseEnd_7629636 := by
    simpa [prefixWord, tailWord_7629636, baseEnd_7629636] using wordTrace_append hprefix tailTrace_7629636
  have hstable : (prefixWord ++ tailWord_7629636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629636).length < 2 ^ (prefixWord ++ tailWord_7629636).sum := by decide
  have hdescent : baseEnd_7629636 < baseStart_7629636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629665 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7629665 : Nat := 118140960795 + 7629665 * 2 ^ 59
def prefixEnd_7629665 : Nat := 4983230072969 + 3 ^ 40 * 7629665 * 2
def baseEnd_7629665 : Nat := 3917685377785996634299315

theorem tailTrace_7629665 : CollatzResearch.WordTrace tailWord_7629665 prefixEnd_7629665 3917685377785996634299315 := by
  unfold tailWord_7629665
  simp only [CollatzResearch.WordTrace]
  refine ⟨278276743904034222886554449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185517829269356148591036299 278276743904034222886554449)
  ·
    refine ⟨208707557928025667164915837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278276743904034222886554449 208707557928025667164915837)
    ·
      refine ⟨78265334223009625186843439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208707557928025667164915837 78265334223009625186843439)
      ·
        refine ⟨117398001334514437780265159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78265334223009625186843439 117398001334514437780265159)
        ·
          refine ⟨176097002001771656670397739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117398001334514437780265159 176097002001771656670397739)
          ·
            refine ⟨264145503002657485005596609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176097002001771656670397739 264145503002657485005596609)
            ·
              refine ⟨198109127251993113754197457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264145503002657485005596609 198109127251993113754197457)
              ·
                refine ⟨148581845438994835315648093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198109127251993113754197457 148581845438994835315648093)
                ·
                  refine ⟨55718192039623063243368035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148581845438994835315648093 55718192039623063243368035)
                  ·
                    refine ⟨83577288059434594865052053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55718192039623063243368035 83577288059434594865052053)
                    ·
                      refine ⟨3917685377785996634299315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83577288059434594865052053 3917685377785996634299315)
                      ·
                        rfl

theorem cell23_7629665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7629665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629665 prefixEnd_7629665 := by exact prefixLift 7629665
  have htrace : WordTrace (prefixWord ++ tailWord_7629665) baseStart_7629665 baseEnd_7629665 := by
    simpa [prefixWord, tailWord_7629665, baseEnd_7629665] using wordTrace_append hprefix tailTrace_7629665
  have hstable : (prefixWord ++ tailWord_7629665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629665).length < 2 ^ (prefixWord ++ tailWord_7629665).sum := by decide
  have hdescent : baseEnd_7629665 < baseStart_7629665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629695 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_7629695 : Nat := 118140960795 + 7629695 * 2 ^ 59
def prefixEnd_7629695 : Nat := 4983230072969 + 3 ^ 40 * 7629695 * 2
def baseEnd_7629695 : Nat := 3917700782205631516924177

theorem tailTrace_7629695 : CollatzResearch.WordTrace tailWord_7629695 prefixEnd_7629695 3917700782205631516924177 := by
  unfold tailWord_7629695
  simp only [CollatzResearch.WordTrace]
  refine ⟨278277838093925538010146539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185518558729283692006764359 278277838093925538010146539)
  ·
    refine ⟨417416757140888307015219809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278277838093925538010146539 417416757140888307015219809)
    ·
      refine ⟨313062567855666230261414857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417416757140888307015219809 313062567855666230261414857)
      ·
        refine ⟨234796925891749672696061143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313062567855666230261414857 234796925891749672696061143)
        ·
          refine ⟨352195388837624509044091715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234796925891749672696061143 352195388837624509044091715)
          ·
            refine ⟨528293083256436763566137573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352195388837624509044091715 528293083256436763566137573)
            ·
              refine ⟨99054953110581893168650795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528293083256436763566137573 99054953110581893168650795)
              ·
                refine ⟨148582429665872839752976193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99054953110581893168650795 148582429665872839752976193)
                ·
                  refine ⟨111436822249404629814732145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148582429665872839752976193 111436822249404629814732145)
                  ·
                    refine ⟨83577616687053472361049109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111436822249404629814732145 83577616687053472361049109)
                    ·
                      refine ⟨3917700782205631516924177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83577616687053472361049109 3917700782205631516924177)
                      ·
                        rfl

theorem cell23_7629695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_7629695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629695 prefixEnd_7629695 := by exact prefixLift 7629695
  have htrace : WordTrace (prefixWord ++ tailWord_7629695) baseStart_7629695 baseEnd_7629695 := by
    simpa [prefixWord, tailWord_7629695, baseEnd_7629695] using wordTrace_append hprefix tailTrace_7629695
  have hstable : (prefixWord ++ tailWord_7629695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629695).length < 2 ^ (prefixWord ++ tailWord_7629695).sum := by decide
  have hdescent : baseEnd_7629695 < baseStart_7629695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629719 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_7629719 : Nat := 118140960795 + 7629719 * 2 ^ 59
def prefixEnd_7629719 : Nat := 4983230072969 + 3 ^ 40 * 7629719 * 2
def baseEnd_7629719 : Nat := 3917713105741339423024067

theorem tailTrace_7629719 : CollatzResearch.WordTrace tailWord_7629719 prefixEnd_7629719 3917713105741339423024067 := by
  unfold tailWord_7629719
  simp only [CollatzResearch.WordTrace]
  refine ⟨278278713445838590109020211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185519142297225726739346807 278278713445838590109020211)
  ·
    refine ⟨417418070168757885163530317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278278713445838590109020211 417418070168757885163530317)
    ·
      refine ⟨156531776313284206936323869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417418070168757885163530317 156531776313284206936323869)
      ·
        refine ⟨58699416117481577601121451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156531776313284206936323869 58699416117481577601121451)
        ·
          refine ⟨88049124176222366401682177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58699416117481577601121451 88049124176222366401682177)
          ·
            refine ⟨66036843132166774801261633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88049124176222366401682177 66036843132166774801261633)
            ·
              refine ⟨49527632349125081100946225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66036843132166774801261633 49527632349125081100946225)
              ·
                refine ⟨37145724261843810825709669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49527632349125081100946225 37145724261843810825709669)
                ·
                  refine ⟨6964823299095714529820563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37145724261843810825709669 6964823299095714529820563)
                  ·
                    refine ⟨10447234948643571794730845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6964823299095714529820563 10447234948643571794730845)
                    ·
                      refine ⟨3917713105741339423024067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10447234948643571794730845 3917713105741339423024067)
                      ·
                        rfl

theorem cell23_7629719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_7629719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629719 prefixEnd_7629719 := by exact prefixLift 7629719
  have htrace : WordTrace (prefixWord ++ tailWord_7629719) baseStart_7629719 baseEnd_7629719 := by
    simpa [prefixWord, tailWord_7629719, baseEnd_7629719] using wordTrace_append hprefix tailTrace_7629719
  have hstable : (prefixWord ++ tailWord_7629719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629719).length < 2 ^ (prefixWord ++ tailWord_7629719).sum := by decide
  have hdescent : baseEnd_7629719 < baseStart_7629719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629752 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_7629752 : Nat := 118140960795 + 7629752 * 2 ^ 59
def prefixEnd_7629752 : Nat := 4983230072969 + 3 ^ 40 * 7629752 * 2
def baseEnd_7629752 : Nat := 1305910016867645931303805

theorem tailTrace_7629752 : CollatzResearch.WordTrace tailWord_7629752 prefixEnd_7629752 1305910016867645931303805 := by
  unfold tailWord_7629752
  simp only [CollatzResearch.WordTrace]
  refine ⟨139139958527359518372485755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185519944703146024496647673 139139958527359518372485755)
  ·
    refine ⟨208709937791039277558728633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139139958527359518372485755 208709937791039277558728633)
    ·
      refine ⟨156532453343279458169046475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208709937791039277558728633 156532453343279458169046475)
      ·
        refine ⟨234798680014919187253569713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156532453343279458169046475 234798680014919187253569713)
        ·
          refine ⟨176099010011189390440177285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234798680014919187253569713 176099010011189390440177285)
          ·
            refine ⟨33018564377098010707533241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176099010011189390440177285 33018564377098010707533241)
            ·
              refine ⟨24763923282823508030649931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33018564377098010707533241 24763923282823508030649931)
              ·
                refine ⟨37145884924235262045974897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24763923282823508030649931 37145884924235262045974897)
                ·
                  refine ⟨27859413693176446534481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37145884924235262045974897 27859413693176446534481173)
                  ·
                    refine ⟨1305910016867645931303805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27859413693176446534481173 1305910016867645931303805)
                    ·
                      rfl

theorem cell23_7629752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_7629752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629752 prefixEnd_7629752 := by exact prefixLift 7629752
  have htrace : WordTrace (prefixWord ++ tailWord_7629752) baseStart_7629752 baseEnd_7629752 := by
    simpa [prefixWord, tailWord_7629752, baseEnd_7629752] using wordTrace_append hprefix tailTrace_7629752
  have hstable : (prefixWord ++ tailWord_7629752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629752).length < 2 ^ (prefixWord ++ tailWord_7629752).sum := by decide
  have hdescent : baseEnd_7629752 < baseStart_7629752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629753 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7629753 : Nat := 118140960795 + 7629753 * 2 ^ 59
def prefixEnd_7629753 : Nat := 4983230072969 + 3 ^ 40 * 7629753 * 2
def baseEnd_7629753 : Nat := 3917730564083592289998911

theorem tailTrace_7629753 : CollatzResearch.WordTrace tailWord_7629753 prefixEnd_7629753 3917730564083592289998911 := by
  unfold tailWord_7629753
  simp only [CollatzResearch.WordTrace]
  refine ⟨278279953527715413915757913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185519969018476942610505275 278279953527715413915757913)
  ·
    refine ⟨208709965145786560436818435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278279953527715413915757913 208709965145786560436818435)
    ·
      refine ⟨313064947718679840655227653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208709965145786560436818435 313064947718679840655227653)
      ·
        refine ⟨58699677697252470122855185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313064947718679840655227653 58699677697252470122855185)
        ·
          refine ⟨44024758272939352592141389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58699677697252470122855185 44024758272939352592141389)
          ·
            refine ⟨16509284352352257222053021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44024758272939352592141389 16509284352352257222053021)
            ·
              refine ⟨6190981632132096458269883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16509284352352257222053021 6190981632132096458269883)
              ·
                refine ⟨9286472448198144687404825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6190981632132096458269883 9286472448198144687404825)
                ·
                  refine ⟨6964854336148608515553619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9286472448198144687404825 6964854336148608515553619)
                  ·
                    refine ⟨10447281504222912773330429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6964854336148608515553619 10447281504222912773330429)
                    ·
                      refine ⟨3917730564083592289998911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10447281504222912773330429 3917730564083592289998911)
                      ·
                        rfl

theorem cell23_7629753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7629753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629753 prefixEnd_7629753 := by exact prefixLift 7629753
  have htrace : WordTrace (prefixWord ++ tailWord_7629753) baseStart_7629753 baseEnd_7629753 := by
    simpa [prefixWord, tailWord_7629753, baseEnd_7629753] using wordTrace_append hprefix tailTrace_7629753
  have hstable : (prefixWord ++ tailWord_7629753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629753).length < 2 ^ (prefixWord ++ tailWord_7629753).sum := by decide
  have hdescent : baseEnd_7629753 < baseStart_7629753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629759 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 1, 4, 2]
def baseStart_7629759 : Nat := 118140960795 + 7629759 * 2 ^ 59
def prefixEnd_7629759 : Nat := 4983230072969 + 3 ^ 40 * 7629759 * 2
def baseEnd_7629759 : Nat := 3917733644967519266523883

theorem tailTrace_7629759 : CollatzResearch.WordTrace tailWord_7629759 prefixEnd_7629759 3917733644967519266523883 := by
  unfold tailWord_7629759
  simp only [CollatzResearch.WordTrace]
  refine ⟨278280172365693676940476331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185520114910462451293650887 278280172365693676940476331)
  ·
    refine ⟨417420258548540515410714497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278280172365693676940476331 417420258548540515410714497)
    ·
      refine ⟨313065193911405386558035873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417420258548540515410714497 313065193911405386558035873)
      ·
        refine ⟨234798895433554039918526905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313065193911405386558035873 234798895433554039918526905)
        ·
          refine ⟨176099171575165529938895179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234798895433554039918526905 176099171575165529938895179)
          ·
            refine ⟨264148757362748294908342769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176099171575165529938895179 264148757362748294908342769)
            ·
              refine ⟨198111568022061221181257077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264148757362748294908342769 198111568022061221181257077)
              ·
                refine ⟨18572959502068239485742851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198111568022061221181257077 18572959502068239485742851)
                ·
                  refine ⟨27859439253102359228614277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18572959502068239485742851 27859439253102359228614277)
                  ·
                    refine ⟨5223644859956692355365177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27859439253102359228614277 5223644859956692355365177)
                    ·
                      refine ⟨3917733644967519266523883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223644859956692355365177 3917733644967519266523883)
                      ·
                        rfl

theorem cell23_7629759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_7629759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629759 prefixEnd_7629759 := by exact prefixLift 7629759
  have htrace : WordTrace (prefixWord ++ tailWord_7629759) baseStart_7629759 baseEnd_7629759 := by
    simpa [prefixWord, tailWord_7629759, baseEnd_7629759] using wordTrace_append hprefix tailTrace_7629759
  have hstable : (prefixWord ++ tailWord_7629759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629759).length < 2 ^ (prefixWord ++ tailWord_7629759).sum := by decide
  have hdescent : baseEnd_7629759 < baseStart_7629759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629799 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 7]
def baseStart_7629799 : Nat := 118140960795 + 7629799 * 2 ^ 59
def prefixEnd_7629799 : Nat := 4983230072969 + 3 ^ 40 * 7629799 * 2
def baseEnd_7629799 : Nat := 435306020465966567780411

theorem tailTrace_7629799 : CollatzResearch.WordTrace tailWord_7629799 prefixEnd_7629799 435306020465966567780411 := by
  unfold tailWord_7629799
  simp only [CollatzResearch.WordTrace]
  refine ⟨278281631285548763771932451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185521087523699175847954967 278281631285548763771932451)
  ·
    refine ⟨417422446928323145657898677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278281631285548763771932451 417422446928323145657898677)
    ·
      refine ⟨39133354399530294905428001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 417422446928323145657898677 39133354399530294905428001)
      ·
        refine ⟨29350015799647721179071001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39133354399530294905428001 29350015799647721179071001)
        ·
          refine ⟨22012511849735790884303251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29350015799647721179071001 22012511849735790884303251)
          ·
            refine ⟨33018767774603686326454877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22012511849735790884303251 33018767774603686326454877)
            ·
              refine ⟨12382037915476382372420579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33018767774603686326454877 12382037915476382372420579)
              ·
                refine ⟨18573056873214573558630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12382037915476382372420579 18573056873214573558630869)
                ·
                  refine ⟨435306020465966567780411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18573056873214573558630869 435306020465966567780411)
                  ·
                    rfl

theorem cell23_7629799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 7].length) (baseStart_7629799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629799 prefixEnd_7629799 := by exact prefixLift 7629799
  have htrace : WordTrace (prefixWord ++ tailWord_7629799) baseStart_7629799 baseEnd_7629799 := by
    simpa [prefixWord, tailWord_7629799, baseEnd_7629799] using wordTrace_append hprefix tailTrace_7629799
  have hstable : (prefixWord ++ tailWord_7629799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629799).length < 2 ^ (prefixWord ++ tailWord_7629799).sum := by decide
  have hdescent : baseEnd_7629799 < baseStart_7629799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629829 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_7629829 : Nat := 118140960795 + 7629829 * 2 ^ 59
def prefixEnd_7629829 : Nat := 4983230072969 + 3 ^ 40 * 7629829 * 2
def baseEnd_7629829 : Nat := 1305923196204444664216187

theorem tailTrace_7629829 : CollatzResearch.WordTrace tailWord_7629829 prefixEnd_7629829 1305923196204444664216187 := by
  unfold tailWord_7629829
  simp only [CollatzResearch.WordTrace]
  refine ⟨278282725475440078895524541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185521816983626719263683027 278282725475440078895524541)
  ·
    refine ⟨104356022053290029585821703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278282725475440078895524541 104356022053290029585821703)
    ·
      refine ⟨156534033079935044378732555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104356022053290029585821703 156534033079935044378732555)
      ·
        refine ⟨234801049619902566568098833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156534033079935044378732555 234801049619902566568098833)
        ·
          refine ⟨176100787214926924926074125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234801049619902566568098833 176100787214926924926074125)
          ·
            refine ⟨66037795205597596847277797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176100787214926924926074125 66037795205597596847277797)
            ·
              refine ⟨12382086601049549408864587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66037795205597596847277797 12382086601049549408864587)
              ·
                refine ⟨18573129901574324113296881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12382086601049549408864587 18573129901574324113296881)
                ·
                  refine ⟨13929847426180743084972661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18573129901574324113296881 13929847426180743084972661)
                  ·
                    refine ⟨1305923196204444664216187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13929847426180743084972661 1305923196204444664216187)
                    ·
                      rfl

theorem cell23_7629829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_7629829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629829 prefixEnd_7629829 := by exact prefixLift 7629829
  have htrace : WordTrace (prefixWord ++ tailWord_7629829) baseStart_7629829 baseEnd_7629829 := by
    simpa [prefixWord, tailWord_7629829, baseEnd_7629829] using wordTrace_append hprefix tailTrace_7629829
  have hstable : (prefixWord ++ tailWord_7629829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629829).length < 2 ^ (prefixWord ++ tailWord_7629829).sum := by decide
  have hdescent : baseEnd_7629829 < baseStart_7629829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629849 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_7629849 : Nat := 118140960795 + 7629849 * 2 ^ 59
def prefixEnd_7629849 : Nat := 4983230072969 + 3 ^ 40 * 7629849 * 2
def baseEnd_7629849 : Nat := 3917779858226423914398469

theorem tailTrace_7629849 : CollatzResearch.WordTrace tailWord_7629849 prefixEnd_7629849 3917779858226423914398469 := by
  unfold tailWord_7629849
  simp only [CollatzResearch.WordTrace]
  refine ⟨278283454935367622311252601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185522303290245081540835067 278283454935367622311252601)
  ·
    refine ⟨208712591201525716733439451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278283454935367622311252601 208712591201525716733439451)
    ·
      refine ⟨313068886802288575100159177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208712591201525716733439451 313068886802288575100159177)
      ·
        refine ⟨234801665101716431325119383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313068886802288575100159177 234801665101716431325119383)
        ·
          refine ⟨352202497652574646987679075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234801665101716431325119383 352202497652574646987679075)
          ·
            refine ⟨528303746478861970481518613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352202497652574646987679075 528303746478861970481518613)
            ·
              refine ⟨24764238116196654866321185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 528303746478861970481518613 24764238116196654866321185)
              ·
                refine ⟨18573178587147491149740889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24764238116196654866321185 18573178587147491149740889)
                ·
                  refine ⟨13929883940360618362305667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18573178587147491149740889 13929883940360618362305667)
                  ·
                    refine ⟨20894825910540927543458501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13929883940360618362305667 20894825910540927543458501)
                    ·
                      refine ⟨3917779858226423914398469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20894825910540927543458501 3917779858226423914398469)
                      ·
                        rfl

theorem cell23_7629849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_7629849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629849 prefixEnd_7629849 := by exact prefixLift 7629849
  have htrace : WordTrace (prefixWord ++ tailWord_7629849) baseStart_7629849 baseEnd_7629849 := by
    simpa [prefixWord, tailWord_7629849, baseEnd_7629849] using wordTrace_append hprefix tailTrace_7629849
  have hstable : (prefixWord ++ tailWord_7629849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629849).length < 2 ^ (prefixWord ++ tailWord_7629849).sum := by decide
  have hdescent : baseEnd_7629849 < baseStart_7629849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629906 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_7629906 : Nat := 118140960795 + 7629906 * 2 ^ 59
def prefixEnd_7629906 : Nat := 4983230072969 + 3 ^ 40 * 7629906 * 2
def baseEnd_7629906 : Nat := 435312125180414465709523

theorem tailTrace_7629906 : CollatzResearch.WordTrace tailWord_7629906 prefixEnd_7629906 435312125180414465709523 := by
  unfold tailWord_7629906
  simp only [CollatzResearch.WordTrace]
  refine ⟨69571383474040280261519393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185523689264107414030718381 69571383474040280261519393)
  ·
    refine ⟨52178537605530210196139545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69571383474040280261519393 52178537605530210196139545)
    ·
      refine ⟨39133903204147657647104659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52178537605530210196139545 39133903204147657647104659)
      ·
        refine ⟨58700854806221486470656989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39133903204147657647104659 58700854806221486470656989)
        ·
          refine ⟨22012820552333057426496371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58700854806221486470656989 22012820552333057426496371)
          ·
            refine ⟨33019230828499586139744557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22012820552333057426496371 33019230828499586139744557)
            ·
              refine ⟨12382211560687344802404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33019230828499586139744557 12382211560687344802404209)
              ·
                refine ⟨9286658670515508601803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12382211560687344802404209 9286658670515508601803157)
                ·
                  refine ⟨435312125180414465709523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9286658670515508601803157 435312125180414465709523)
                  ·
                    rfl

theorem cell23_7629906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_7629906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629906 prefixEnd_7629906 := by exact prefixLift 7629906
  have htrace : WordTrace (prefixWord ++ tailWord_7629906) baseStart_7629906 baseEnd_7629906 := by
    simpa [prefixWord, tailWord_7629906, baseEnd_7629906] using wordTrace_append hprefix tailTrace_7629906
  have hstable : (prefixWord ++ tailWord_7629906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629906).length < 2 ^ (prefixWord ++ tailWord_7629906).sum := by decide
  have hdescent : baseEnd_7629906 < baseStart_7629906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629933 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_7629933 : Nat := 118140960795 + 7629933 * 2 ^ 59
def prefixEnd_7629933 : Nat := 4983230072969 + 3 ^ 40 * 7629933 * 2
def baseEnd_7629933 : Nat := 3917822990601401585748083

theorem tailTrace_7629933 : CollatzResearch.WordTrace tailWord_7629933 prefixEnd_7629933 3917822990601401585748083 := by
  unfold tailWord_7629933
  simp only [CollatzResearch.WordTrace]
  refine ⟨278286518667063304657310453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185524345778042203104873635 278286518667063304657310453)
  ·
    refine ⟨26089361125037184811622855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278286518667063304657310453 26089361125037184811622855)
    ·
      refine ⟨39134041687555777217434283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26089361125037184811622855 39134041687555777217434283)
      ·
        refine ⟨58701062531333665826151425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39134041687555777217434283 58701062531333665826151425)
        ·
          refine ⟨44025796898500249369613569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58701062531333665826151425 44025796898500249369613569)
          ·
            refine ⟨33019347673875187027210177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44025796898500249369613569 33019347673875187027210177)
            ·
              refine ⟨24764510755406390270407633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33019347673875187027210177 24764510755406390270407633)
              ·
                refine ⟨18573383066554792702805725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24764510755406390270407633 18573383066554792702805725)
                ·
                  refine ⟨6965018649958047263552147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18573383066554792702805725 6965018649958047263552147)
                  ·
                    refine ⟨10447527974937070895328221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965018649958047263552147 10447527974937070895328221)
                    ·
                      refine ⟨3917822990601401585748083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10447527974937070895328221 3917822990601401585748083)
                      ·
                        rfl

theorem cell23_7629933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_7629933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629933 prefixEnd_7629933 := by exact prefixLift 7629933
  have htrace : WordTrace (prefixWord ++ tailWord_7629933) baseStart_7629933 baseEnd_7629933 := by
    simpa [prefixWord, tailWord_7629933, baseEnd_7629933] using wordTrace_append hprefix tailTrace_7629933
  have hstable : (prefixWord ++ tailWord_7629933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629933).length < 2 ^ (prefixWord ++ tailWord_7629933).sum := by decide
  have hdescent : baseEnd_7629933 < baseStart_7629933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629936 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_7629936 : Nat := 118140960795 + 7629936 * 2 ^ 59
def prefixEnd_7629936 : Nat := 4983230072969 + 3 ^ 40 * 7629936 * 2
def baseEnd_7629936 : Nat := 1305941510347788358003523

theorem tailTrace_7629936 : CollatzResearch.WordTrace tailWord_7629936 prefixEnd_7629936 1305941510347788358003523 := by
  unfold tailWord_7629936
  simp only [CollatzResearch.WordTrace]
  refine ⟨139143314043026218084834831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185524418724034957446446441 139143314043026218084834831)
  ·
    refine ⟨208714971064539327127252247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139143314043026218084834831 208714971064539327127252247)
    ·
      refine ⟨313072456596808990690878371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208714971064539327127252247 313072456596808990690878371)
      ·
        refine ⟨469608684895213486036317557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313072456596808990690878371 469608684895213486036317557)
        ·
          refine ⟨44025814208926264315904771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 469608684895213486036317557 44025814208926264315904771)
          ·
            refine ⟨66038721313389396473857157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44025814208926264315904771 66038721313389396473857157)
            ·
              refine ⟨12382260246260511838848217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66038721313389396473857157 12382260246260511838848217)
              ·
                refine ⟨9286695184695383879136163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12382260246260511838848217 9286695184695383879136163)
                ·
                  refine ⟨13930042777043075818704245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9286695184695383879136163 13930042777043075818704245)
                  ·
                    refine ⟨1305941510347788358003523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13930042777043075818704245 1305941510347788358003523)
                    ·
                      rfl

theorem cell23_7629936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_7629936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629936 prefixEnd_7629936 := by exact prefixLift 7629936
  have htrace : WordTrace (prefixWord ++ tailWord_7629936) baseStart_7629936 baseEnd_7629936 := by
    simpa [prefixWord, tailWord_7629936, baseEnd_7629936] using wordTrace_append hprefix tailTrace_7629936
  have hstable : (prefixWord ++ tailWord_7629936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629936).length < 2 ^ (prefixWord ++ tailWord_7629936).sum := by decide
  have hdescent : baseEnd_7629936 < baseStart_7629936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629949 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_7629949 : Nat := 118140960795 + 7629949 * 2 ^ 59
def prefixEnd_7629949 : Nat := 4983230072969 + 3 ^ 40 * 7629949 * 2
def baseEnd_7629949 : Nat := 1305943735430624507716003

theorem tailTrace_7629949 : CollatzResearch.WordTrace tailWord_7629949 prefixEnd_7629949 1305943735430624507716003 := by
  unfold tailWord_7629949
  simp only [CollatzResearch.WordTrace]
  refine ⟨278287102235005339389892901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185524734823336892926595267 278287102235005339389892901)
  ·
    refine ⟨52178831669063501135604919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278287102235005339389892901 52178831669063501135604919)
    ·
      refine ⟨78268247503595251703407379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52178831669063501135604919 78268247503595251703407379)
      ·
        refine ⟨117402371255392877555111069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78268247503595251703407379 117402371255392877555111069)
        ·
          refine ⟨44025889220772329083166651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117402371255392877555111069 44025889220772329083166651)
          ·
            refine ⟨66038833831158493624749977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44025889220772329083166651 66038833831158493624749977)
            ·
              refine ⟨49529125373368870218562483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66038833831158493624749977 49529125373368870218562483)
              ·
                refine ⟨74293688060053305327843725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49529125373368870218562483 74293688060053305327843725)
                ·
                  refine ⟨27860133022519989497941397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74293688060053305327843725 27860133022519989497941397)
                  ·
                    refine ⟨1305943735430624507716003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27860133022519989497941397 1305943735430624507716003)
                    ·
                      rfl

theorem cell23_7629949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_7629949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629949 prefixEnd_7629949 := by exact prefixLift 7629949
  have htrace : WordTrace (prefixWord ++ tailWord_7629949) baseStart_7629949 baseEnd_7629949 := by
    simpa [prefixWord, tailWord_7629949, baseEnd_7629949] using wordTrace_append hprefix tailTrace_7629949
  have hstable : (prefixWord ++ tailWord_7629949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629949).length < 2 ^ (prefixWord ++ tailWord_7629949).sum := by decide
  have hdescent : baseEnd_7629949 < baseStart_7629949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629960 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7629960 : Nat := 118140960795 + 7629960 * 2 ^ 59
def prefixEnd_7629960 : Nat := 4983230072969 + 3 ^ 40 * 7629960 * 2
def baseEnd_7629960 : Nat := 3917836854579072980110459

theorem tailTrace_7629960 : CollatzResearch.WordTrace tailWord_7629960 prefixEnd_7629960 3917836854579072980110459 := by
  unfold tailWord_7629960
  simp only [CollatzResearch.WordTrace]
  refine ⟨139143751718982744134271667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185525002291976992179028889 139143751718982744134271667)
  ·
    refine ⟨208715627578474116201407501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139143751718982744134271667 208715627578474116201407501)
    ·
      refine ⟨78268360341927793575527813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208715627578474116201407501 78268360341927793575527813)
      ·
        refine ⟨14675317564111461295411465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78268360341927793575527813 14675317564111461295411465)
        ·
          refine ⟨11006488173083595971558599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14675317564111461295411465 11006488173083595971558599)
          ·
            refine ⟨16509732259625393957337899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006488173083595971558599 16509732259625393957337899)
            ·
              refine ⟨24764598389438090936006849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16509732259625393957337899 24764598389438090936006849)
              ·
                refine ⟨18573448792078568202005137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24764598389438090936006849 18573448792078568202005137)
                ·
                  refine ⟨13930086594058926151503853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18573448792078568202005137 13930086594058926151503853)
                  ·
                    refine ⟨5223782472772097306813945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13930086594058926151503853 5223782472772097306813945)
                    ·
                      refine ⟨3917836854579072980110459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223782472772097306813945 3917836854579072980110459)
                      ·
                        rfl

theorem cell23_7629960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7629960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629960 prefixEnd_7629960 := by exact prefixLift 7629960
  have htrace : WordTrace (prefixWord ++ tailWord_7629960) baseStart_7629960 baseEnd_7629960 := by
    simpa [prefixWord, tailWord_7629960, baseEnd_7629960] using wordTrace_append hprefix tailTrace_7629960
  have hstable : (prefixWord ++ tailWord_7629960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629960).length < 2 ^ (prefixWord ++ tailWord_7629960).sum := by decide
  have hdescent : baseEnd_7629960 < baseStart_7629960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629973 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_7629973 : Nat := 118140960795 + 7629973 * 2 ^ 59
def prefixEnd_7629973 : Nat := 4983230072969 + 3 ^ 40 * 7629973 * 2
def baseEnd_7629973 : Nat := 3917843529827581429247899

theorem tailTrace_7629973 : CollatzResearch.WordTrace tailWord_7629973 prefixEnd_7629973 3917843529827581429247899 := by
  unfold tailWord_7629973
  simp only [CollatzResearch.WordTrace]
  refine ⟨278287977586918391488766573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185525318391278927659177715 278287977586918391488766573)
  ·
    refine ⟨104357991595094396808287465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278287977586918391488766573 104357991595094396808287465)
    ·
      refine ⟨78268493696320797606215599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104357991595094396808287465 78268493696320797606215599)
      ·
        refine ⟨117402740544481196409323399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78268493696320797606215599 117402740544481196409323399)
        ·
          refine ⟨176104110816721794613985099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117402740544481196409323399 176104110816721794613985099)
          ·
            refine ⟨264156166225082691920977649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176104110816721794613985099 264156166225082691920977649)
            ·
              refine ⟨198117124668812018940733237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264156166225082691920977649 198117124668812018940733237)
              ·
                refine ⟨18573480437701126775693741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198117124668812018940733237 18573480437701126775693741)
                ·
                  refine ⟨6965055164137922540885153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18573480437701126775693741 6965055164137922540885153)
                  ·
                    refine ⟨5223791373103441905663865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6965055164137922540885153 5223791373103441905663865)
                    ·
                      refine ⟨3917843529827581429247899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223791373103441905663865 3917843529827581429247899)
                      ·
                        rfl

theorem cell23_7629973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_7629973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629973 prefixEnd_7629973 := by exact prefixLift 7629973
  have htrace : WordTrace (prefixWord ++ tailWord_7629973) baseStart_7629973 baseEnd_7629973 := by
    simpa [prefixWord, tailWord_7629973, baseEnd_7629973] using wordTrace_append hprefix tailTrace_7629973
  have hstable : (prefixWord ++ tailWord_7629973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629973).length < 2 ^ (prefixWord ++ tailWord_7629973).sum := by decide
  have hdescent : baseEnd_7629973 < baseStart_7629973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7629976 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7629976 : Nat := 118140960795 + 7629976 * 2 ^ 59
def prefixEnd_7629976 : Nat := 4983230072969 + 3 ^ 40 * 7629976 * 2
def baseEnd_7629976 : Nat := 3917845070269544917510385

theorem tailTrace_7629976 : CollatzResearch.WordTrace tailWord_7629976 prefixEnd_7629976 3917845070269544917510385 := by
  unfold tailWord_7629976
  simp only [CollatzResearch.WordTrace]
  refine ⟨139144043502953761500562891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185525391337271682000750521 139144043502953761500562891)
  ·
    refine ⟨208716065254430642250844337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139144043502953761500562891 208716065254430642250844337)
    ·
      refine ⟨156537048940822981688133253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208716065254430642250844337 156537048940822981688133253)
      ·
        refine ⟨29350696676404309066524985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156537048940822981688133253 29350696676404309066524985)
        ·
          refine ⟨22013022507303231799893739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29350696676404309066524985 22013022507303231799893739)
          ·
            refine ⟨33019533760954847699840609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22013022507303231799893739 33019533760954847699840609)
            ·
              refine ⟨24764650320716135774880457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33019533760954847699840609 24764650320716135774880457)
              ·
                refine ⟨18573487740537101831160343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24764650320716135774880457 18573487740537101831160343)
                ·
                  refine ⟨27860231610805652746740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18573487740537101831160343 27860231610805652746740515)
                  ·
                    refine ⟨41790347416208479120110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27860231610805652746740515 41790347416208479120110773)
                    ·
                      refine ⟨3917845070269544917510385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41790347416208479120110773 3917845070269544917510385)
                      ·
                        rfl

theorem cell23_7629976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7629976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7629976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7629976 prefixEnd_7629976 := by exact prefixLift 7629976
  have htrace : WordTrace (prefixWord ++ tailWord_7629976) baseStart_7629976 baseEnd_7629976 := by
    simpa [prefixWord, tailWord_7629976, baseEnd_7629976] using wordTrace_append hprefix tailTrace_7629976
  have hstable : (prefixWord ++ tailWord_7629976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7629976).length < 2 ^ (prefixWord ++ tailWord_7629976).sum := by decide
  have hdescent : baseEnd_7629976 < baseStart_7629976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7629976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630018 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7630018 : Nat := 118140960795 + 7630018 * 2 ^ 59
def prefixEnd_7630018 : Nat := 4983230072969 + 3 ^ 40 * 7630018 * 2
def baseEnd_7630018 : Nat := 3917866636457033753185193

theorem tailTrace_7630018 : CollatzResearch.WordTrace tailWord_7630018 prefixEnd_7630018 3917866636457033753185193 := by
  unfold tailWord_7630018
  simp only [CollatzResearch.WordTrace]
  refine ⟨69572404717938841043538677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185526412581170242782769805 69572404717938841043538677)
  ·
    refine ⟨6522412942306766347831751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69572404717938841043538677 6522412942306766347831751)
    ·
      refine ⟨9783619413460149521747627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522412942306766347831751 9783619413460149521747627)
      ·
        refine ⟨14675429120190224282621441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9783619413460149521747627 14675429120190224282621441)
        ·
          refine ⟨11006571840142668211966081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14675429120190224282621441 11006571840142668211966081)
          ·
            refine ⟨8254928880107001158974561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11006571840142668211966081 8254928880107001158974561)
            ·
              refine ⟨6191196660080250869230921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254928880107001158974561 6191196660080250869230921)
              ·
                refine ⟨4643397495060188151923191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191196660080250869230921 4643397495060188151923191)
                ·
                  refine ⟨6965096242590282227884787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643397495060188151923191 6965096242590282227884787)
                  ·
                    refine ⟨10447644363885423341827181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965096242590282227884787 10447644363885423341827181)
                    ·
                      refine ⟨3917866636457033753185193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10447644363885423341827181 3917866636457033753185193)
                      ·
                        rfl

theorem cell23_7630018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7630018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630018 prefixEnd_7630018 := by exact prefixLift 7630018
  have htrace : WordTrace (prefixWord ++ tailWord_7630018) baseStart_7630018 baseEnd_7630018 := by
    simpa [prefixWord, tailWord_7630018, baseEnd_7630018] using wordTrace_append hprefix tailTrace_7630018
  have hstable : (prefixWord ++ tailWord_7630018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630018).length < 2 ^ (prefixWord ++ tailWord_7630018).sum := by decide
  have hdescent : baseEnd_7630018 < baseStart_7630018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630039 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 8]
def baseStart_7630039 : Nat := 118140960795 + 7630039 * 2 ^ 59
def prefixEnd_7630039 : Nat := 4983230072969 + 3 ^ 40 * 7630039 * 2
def baseEnd_7630039 : Nat := 1305959139850259390340865

theorem tailTrace_7630039 : CollatzResearch.WordTrace tailWord_7630039 prefixEnd_7630039 1305959139850259390340865 := by
  unfold tailWord_7630039
  simp only [CollatzResearch.WordTrace]
  refine ⟨278290384804679284760669171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185526923203119523173779447 278290384804679284760669171)
  ·
    refine ⟨417435577207018927141003757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278290384804679284760669171 417435577207018927141003757)
    ·
      refine ⟨156538341452632097677876409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417435577207018927141003757 156538341452632097677876409)
      ·
        refine ⟨117403756089474073258407307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156538341452632097677876409 117403756089474073258407307)
        ·
          refine ⟨176105634134211109887610961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117403756089474073258407307 176105634134211109887610961)
          ·
            refine ⟨132079225600658332415708221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176105634134211109887610961 132079225600658332415708221)
            ·
              refine ⟨49529709600246874655890583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132079225600658332415708221 49529709600246874655890583)
              ·
                refine ⟨74294564400370311983835875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49529709600246874655890583 74294564400370311983835875)
                ·
                  refine ⟨111441846600555467975753813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74294564400370311983835875 111441846600555467975753813)
                  ·
                    refine ⟨1305959139850259390340865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111441846600555467975753813 1305959139850259390340865)
                    ·
                      rfl

theorem cell23_7630039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_7630039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630039 prefixEnd_7630039 := by exact prefixLift 7630039
  have htrace : WordTrace (prefixWord ++ tailWord_7630039) baseStart_7630039 baseEnd_7630039 := by
    simpa [prefixWord, tailWord_7630039, baseEnd_7630039] using wordTrace_append hprefix tailTrace_7630039
  have hstable : (prefixWord ++ tailWord_7630039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630039).length < 2 ^ (prefixWord ++ tailWord_7630039).sum := by decide
  have hdescent : baseEnd_7630039 < baseStart_7630039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630067 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 1, 3, 2]
def baseStart_7630067 : Nat := 118140960795 + 7630067 * 2 ^ 59
def prefixEnd_7630067 : Nat := 4983230072969 + 3 ^ 40 * 7630067 * 2
def baseEnd_7630067 : Nat := 3917891797009104061472467

theorem tailTrace_7630067 : CollatzResearch.WordTrace tailWord_7630067 prefixEnd_7630067 3917891797009104061472467 := by
  unfold tailWord_7630067
  simp only [CollatzResearch.WordTrace]
  refine ⟨278291406048577845542688455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185527604032385230361792303 278291406048577845542688455)
  ·
    refine ⟨417437109072866768314032683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278291406048577845542688455 417437109072866768314032683)
    ·
      refine ⟨626155663609300152471049025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417437109072866768314032683 626155663609300152471049025)
      ·
        refine ⟨469616747706975114353286769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626155663609300152471049025 469616747706975114353286769)
        ·
          refine ⟨352212560780231335764965077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469616747706975114353286769 352212560780231335764965077)
          ·
            refine ⟨8254981893286671931991369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352212560780231335764965077 8254981893286671931991369)
            ·
              refine ⟨6191236419965003948993527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254981893286671931991369 6191236419965003948993527)
              ·
                refine ⟨9286854629947505923490291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191236419965003948993527 9286854629947505923490291)
                ·
                  refine ⟨13930281944921258885235437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9286854629947505923490291 13930281944921258885235437)
                  ·
                    refine ⟨5223855729345472081963289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13930281944921258885235437 5223855729345472081963289)
                    ·
                      refine ⟨3917891797009104061472467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223855729345472081963289 3917891797009104061472467)
                      ·
                        rfl

theorem cell23_7630067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 1, 3, 2].length) (baseStart_7630067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630067 prefixEnd_7630067 := by exact prefixLift 7630067
  have htrace : WordTrace (prefixWord ++ tailWord_7630067) baseStart_7630067 baseEnd_7630067 := by
    simpa [prefixWord, tailWord_7630067, baseEnd_7630067] using wordTrace_append hprefix tailTrace_7630067
  have hstable : (prefixWord ++ tailWord_7630067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630067).length < 2 ^ (prefixWord ++ tailWord_7630067).sum := by decide
  have hdescent : baseEnd_7630067 < baseStart_7630067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630097 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_7630097 : Nat := 118140960795 + 7630097 * 2 ^ 59
def prefixEnd_7630097 : Nat := 4983230072969 + 3 ^ 40 * 7630097 * 2
def baseEnd_7630097 : Nat := 3917907201428738944097329

theorem tailTrace_7630097 : CollatzResearch.WordTrace tailWord_7630097 prefixEnd_7630097 3917907201428738944097329 := by
  unfold tailWord_7630097
  simp only [CollatzResearch.WordTrace]
  refine ⟨278292500238469160666280545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185528333492312773777520363 278292500238469160666280545)
  ·
    refine ⟨208719375178851870499710409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278292500238469160666280545 208719375178851870499710409)
    ·
      refine ⟨156539531384138902874782807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208719375178851870499710409 156539531384138902874782807)
      ·
        refine ⟨234809297076208354312174211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156539531384138902874782807 234809297076208354312174211)
        ·
          refine ⟨352213945614312531468261317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234809297076208354312174211 352213945614312531468261317)
          ·
            refine ⟨66040114802683599650298997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352213945614312531468261317 66040114802683599650298997)
            ·
              refine ⟨6191260762751587467215531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66040114802683599650298997 6191260762751587467215531)
              ·
                refine ⟨9286891144127381200823297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191260762751587467215531 9286891144127381200823297)
                ·
                  refine ⟨6965168358095535900617473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9286891144127381200823297 6965168358095535900617473)
                  ·
                    refine ⟨5223876268571651925463105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6965168358095535900617473 5223876268571651925463105)
                    ·
                      refine ⟨3917907201428738944097329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223876268571651925463105 3917907201428738944097329)
                      ·
                        rfl

theorem cell23_7630097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_7630097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630097 prefixEnd_7630097 := by exact prefixLift 7630097
  have htrace : WordTrace (prefixWord ++ tailWord_7630097) baseStart_7630097 baseEnd_7630097 := by
    simpa [prefixWord, tailWord_7630097, baseEnd_7630097] using wordTrace_append hprefix tailTrace_7630097
  have hstable : (prefixWord ++ tailWord_7630097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630097).length < 2 ^ (prefixWord ++ tailWord_7630097).sum := by decide
  have hdescent : baseEnd_7630097 < baseStart_7630097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630116 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_7630116 : Nat := 118140960795 + 7630116 * 2 ^ 59
def prefixEnd_7630116 : Nat := 4983230072969 + 3 ^ 40 * 7630116 * 2
def baseEnd_7630116 : Nat := 1305972319187058123253247

theorem tailTrace_7630116 : CollatzResearch.WordTrace tailWord_7630116 prefixEnd_7630116 1305972319187058123253247 := by
  unfold tailWord_7630116
  simp only [CollatzResearch.WordTrace]
  refine ⟨139146596612700163455611101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185528795483600217940814801 139146596612700163455611101)
  ·
    refine ⟨52179973729762561295854163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139146596612700163455611101 52179973729762561295854163)
    ·
      refine ⟨78269960594643841943781245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52179973729762561295854163 78269960594643841943781245)
      ·
        refine ⟨29351235222991440728917967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78269960594643841943781245 29351235222991440728917967)
        ·
          refine ⟨44026852834487161093376951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29351235222991440728917967 44026852834487161093376951)
          ·
            refine ⟨66040279251730741640065427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44026852834487161093376951 66040279251730741640065427)
            ·
              refine ⟨99060418877596112460098141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66040279251730741640065427 99060418877596112460098141)
              ·
                refine ⟨37147657079098542172536803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99060418877596112460098141 37147657079098542172536803)
                ·
                  refine ⟨55721485618647813258805205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37147657079098542172536803 55721485618647813258805205)
                  ·
                    refine ⟨1305972319187058123253247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55721485618647813258805205 1305972319187058123253247)
                    ·
                      rfl

theorem cell23_7630116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_7630116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630116 prefixEnd_7630116 := by exact prefixLift 7630116
  have htrace : WordTrace (prefixWord ++ tailWord_7630116) baseStart_7630116 baseEnd_7630116 := by
    simpa [prefixWord, tailWord_7630116, baseEnd_7630116] using wordTrace_append hprefix tailTrace_7630116
  have hstable : (prefixWord ++ tailWord_7630116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630116).length < 2 ^ (prefixWord ++ tailWord_7630116).sum := by decide
  have hdescent : baseEnd_7630116 < baseStart_7630116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630120 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 5]
def baseStart_7630120 : Nat := 118140960795 + 7630120 * 2 ^ 59
def prefixEnd_7630120 : Nat := 4983230072969 + 3 ^ 40 * 7630120 * 2
def baseEnd_7630120 : Nat := 435324334609310261567747

theorem tailTrace_7630120 : CollatzResearch.WordTrace tailWord_7630120 prefixEnd_7630120 435324334609310261567747 := by
  unfold tailWord_7630120
  simp only [CollatzResearch.WordTrace]
  refine ⟨139146669558692917797183907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185528892744923890396245209 139146669558692917797183907)
  ·
    refine ⟨208720004338039376695775861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139146669558692917797183907 208720004338039376695775861)
    ·
      refine ⟨19567500406691191565228987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208720004338039376695775861 19567500406691191565228987)
      ·
        refine ⟨29351250610036787347843481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19567500406691191565228987 29351250610036787347843481)
        ·
          refine ⟨22013437957527590510882611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29351250610036787347843481 22013437957527590510882611)
          ·
            refine ⟨33020156936291385766323917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22013437957527590510882611 33020156936291385766323917)
            ·
              refine ⟨12382558851109269662371469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33020156936291385766323917 12382558851109269662371469)
              ·
                refine ⟨4643459569165976123389301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12382558851109269662371469 4643459569165976123389301)
                ·
                  refine ⟨435324334609310261567747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643459569165976123389301 435324334609310261567747)
                  ·
                    rfl

theorem cell23_7630120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 5].length) (baseStart_7630120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630120 prefixEnd_7630120 := by exact prefixLift 7630120
  have htrace : WordTrace (prefixWord ++ tailWord_7630120) baseStart_7630120 baseEnd_7630120 := by
    simpa [prefixWord, tailWord_7630120, baseEnd_7630120] using wordTrace_append hprefix tailTrace_7630120
  have hstable : (prefixWord ++ tailWord_7630120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630120).length < 2 ^ (prefixWord ++ tailWord_7630120).sum := by decide
  have hdescent : baseEnd_7630120 < baseStart_7630120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630133 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7630133 : Nat := 118140960795 + 7630133 * 2 ^ 59
def prefixEnd_7630133 : Nat := 4983230072969 + 3 ^ 40 * 7630133 * 2
def baseEnd_7630133 : Nat := 1305975228910766934415721

theorem tailTrace_7630133 : CollatzResearch.WordTrace tailWord_7630133 prefixEnd_7630133 1305975228910766934415721 := by
  unfold tailWord_7630133
  simp only [CollatzResearch.WordTrace]
  refine ⟨278293813266338738814591053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185529208844225825876394035 278293813266338738814591053)
  ·
    refine ⟨104360179974877027055471645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278293813266338738814591053 104360179974877027055471645)
    ·
      refine ⟨39135067490578885145801867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104360179974877027055471645 39135067490578885145801867)
      ·
        refine ⟨58702601235868327718702801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39135067490578885145801867 58702601235868327718702801)
        ·
          refine ⟨44026950926901245789027101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58702601235868327718702801 44026950926901245789027101)
          ·
            refine ⟨16510106597587967170885163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44026950926901245789027101 16510106597587967170885163)
            ·
              refine ⟨24765159896381950756327745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16510106597587967170885163 24765159896381950756327745)
              ·
                refine ⟨18573869922286463067245809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24765159896381950756327745 18573869922286463067245809)
                ·
                  refine ⟨13930402441714847300434357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18573869922286463067245809 13930402441714847300434357)
                  ·
                    refine ⟨1305975228910766934415721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13930402441714847300434357 1305975228910766934415721)
                    ·
                      rfl

theorem cell23_7630133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7630133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630133 prefixEnd_7630133 := by exact prefixLift 7630133
  have htrace : WordTrace (prefixWord ++ tailWord_7630133) baseStart_7630133 baseEnd_7630133 := by
    simpa [prefixWord, tailWord_7630133, baseEnd_7630133] using wordTrace_append hprefix tailTrace_7630133
  have hstable : (prefixWord ++ tailWord_7630133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630133).length < 2 ^ (prefixWord ++ tailWord_7630133).sum := by decide
  have hdescent : baseEnd_7630133 < baseStart_7630133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630137 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 5]
def baseStart_7630137 : Nat := 118140960795 + 7630137 * 2 ^ 59
def prefixEnd_7630137 : Nat := 4983230072969 + 3 ^ 40 * 7630137 * 2
def baseEnd_7630137 : Nat := 435325304517213198621905

theorem tailTrace_7630137 : CollatzResearch.WordTrace tailWord_7630137 prefixEnd_7630137 435325304517213198621905 := by
  unfold tailWord_7630137
  simp only [CollatzResearch.WordTrace]
  refine ⟨278293959158324247497736665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185529306105549498331824443 278293959158324247497736665)
  ·
    refine ⟨208720469368743185623302499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278293959158324247497736665 208720469368743185623302499)
    ·
      refine ⟨313080704053114778434953749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208720469368743185623302499 313080704053114778434953749)
      ·
        refine ⟨14675658002489755239138457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 313080704053114778434953749 14675658002489755239138457)
        ·
          refine ⟨11006743501867316429353843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14675658002489755239138457 11006743501867316429353843)
          ·
            refine ⟨16510115252800974644030765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006743501867316429353843 16510115252800974644030765)
            ·
              refine ⟨6191293219800365491511537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16510115252800974644030765 6191293219800365491511537)
              ·
                refine ⟨4643469914850274118633653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191293219800365491511537 4643469914850274118633653)
                ·
                  refine ⟨435325304517213198621905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643469914850274118633653 435325304517213198621905)
                  ·
                    rfl

theorem cell23_7630137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 5].length) (baseStart_7630137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630137 prefixEnd_7630137 := by exact prefixLift 7630137
  have htrace : WordTrace (prefixWord ++ tailWord_7630137) baseStart_7630137 baseEnd_7630137 := by
    simpa [prefixWord, tailWord_7630137, baseEnd_7630137] using wordTrace_append hprefix tailTrace_7630137
  have hstable : (prefixWord ++ tailWord_7630137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630137).length < 2 ^ (prefixWord ++ tailWord_7630137).sum := by decide
  have hdescent : baseEnd_7630137 < baseStart_7630137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630153 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 2, 4, 2]
def baseStart_7630153 : Nat := 118140960795 + 7630153 * 2 ^ 59
def prefixEnd_7630153 : Nat := 4983230072969 + 3 ^ 40 * 7630153 * 2
def baseEnd_7630153 : Nat := 3917935956345390724997071

theorem tailTrace_7630153 : CollatzResearch.WordTrace tailWord_7630153 prefixEnd_7630153 3917935956345390724997071 := by
  unfold tailWord_7630153
  simp only [CollatzResearch.WordTrace]
  refine ⟨278294542726266282230319113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185529695150844188153546075 278294542726266282230319113)
  ·
    refine ⟨208720907044699711672739335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278294542726266282230319113 208720907044699711672739335)
    ·
      refine ⟨313081360567049567509109003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208720907044699711672739335 313081360567049567509109003)
      ·
        refine ⟨469622040850574351263663505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313081360567049567509109003 469622040850574351263663505)
        ·
          refine ⟨352216530637930763447747629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469622040850574351263663505 352216530637930763447747629)
          ·
            refine ⟨132081198989224036292905361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352216530637930763447747629 132081198989224036292905361)
            ·
              refine ⟨99060899241918027219679021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132081198989224036292905361 99060899241918027219679021)
              ·
                refine ⟨37147837215719260207379633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99060899241918027219679021 37147837215719260207379633)
                ·
                  refine ⟨27860877911789445155534725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37147837215719260207379633 27860877911789445155534725)
                  ·
                    refine ⟨5223914608460520966662761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27860877911789445155534725 5223914608460520966662761)
                    ·
                      refine ⟨3917935956345390724997071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5223914608460520966662761 3917935956345390724997071)
                      ·
                        rfl

theorem cell23_7630153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 4, 2].length) (baseStart_7630153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630153 prefixEnd_7630153 := by exact prefixLift 7630153
  have htrace : WordTrace (prefixWord ++ tailWord_7630153) baseStart_7630153 baseEnd_7630153 := by
    simpa [prefixWord, tailWord_7630153, baseEnd_7630153] using wordTrace_append hprefix tailTrace_7630153
  have hstable : (prefixWord ++ tailWord_7630153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630153).length < 2 ^ (prefixWord ++ tailWord_7630153).sum := by decide
  have hdescent : baseEnd_7630153 < baseStart_7630153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630220 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_7630220 : Nat := 118140960795 + 7630220 * 2 ^ 59
def prefixEnd_7630220 : Nat := 4983230072969 + 3 ^ 40 * 7630220 * 2
def baseEnd_7630220 : Nat := 3917970359549241962859263

theorem tailTrace_7630220 : CollatzResearch.WordTrace tailWord_7630220 prefixEnd_7630220 3917970359549241962859263 := by
  unfold tailWord_7630220
  simp only [CollatzResearch.WordTrace]
  refine ⟨139148493208511776336504057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185531324278015701782005409 139148493208511776336504057)
  ·
    refine ⟨104361369906383832252378043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139148493208511776336504057 104361369906383832252378043)
    ·
      refine ⟨156542054859575748378567065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104361369906383832252378043 156542054859575748378567065)
      ·
        refine ⟨117406541144681811283925299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156542054859575748378567065 117406541144681811283925299)
        ·
          refine ⟨176109811717022716925887949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117406541144681811283925299 176109811717022716925887949)
          ·
            refine ⟨66041179393883518847207981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176109811717022716925887949 66041179393883518847207981)
            ·
              refine ⟨24765442272706319567702993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66041179393883518847207981 24765442272706319567702993)
              ·
                refine ⟨18574081704529739675777245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24765442272706319567702993 18574081704529739675777245)
                ·
                  refine ⟨6965280639198652378416467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18574081704529739675777245 6965280639198652378416467)
                  ·
                    refine ⟨10447920958797978567624701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965280639198652378416467 10447920958797978567624701)
                    ·
                      refine ⟨3917970359549241962859263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10447920958797978567624701 3917970359549241962859263)
                      ·
                        rfl

theorem cell23_7630220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_7630220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630220 prefixEnd_7630220 := by exact prefixLift 7630220
  have htrace : WordTrace (prefixWord ++ tailWord_7630220) baseStart_7630220 baseEnd_7630220 := by
    simpa [prefixWord, tailWord_7630220, baseEnd_7630220] using wordTrace_append hprefix tailTrace_7630220
  have hstable : (prefixWord ++ tailWord_7630220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630220).length < 2 ^ (prefixWord ++ tailWord_7630220).sum := by decide
  have hdescent : baseEnd_7630220 < baseStart_7630220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630263 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_7630263 : Nat := 118140960795 + 7630263 * 2 ^ 59
def prefixEnd_7630263 : Nat := 4983230072969 + 3 ^ 40 * 7630263 * 2
def baseEnd_7630263 : Nat := 3917992439217385294621565

theorem tailTrace_7630263 : CollatzResearch.WordTrace tailWord_7630263 prefixEnd_7630263 3917992439217385294621565 := by
  unfold tailWord_7630263
  simp only [CollatzResearch.WordTrace]
  refine ⟨278298554755867771016823443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185532369837245180677882295 278298554755867771016823443)
  ·
    refine ⟨417447832133801656525235165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278298554755867771016823443 417447832133801656525235165)
    ·
      refine ⟨156542937050175621196963187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417447832133801656525235165 156542937050175621196963187)
      ·
        refine ⟨234814405575263431795444781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156542937050175621196963187 234814405575263431795444781)
        ·
          refine ⟨88055402090723786923291793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234814405575263431795444781 88055402090723786923291793)
          ·
            refine ⟨66041551568042840192468845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88055402090723786923291793 66041551568042840192468845)
            ·
              refine ⟨24765581838016065072175817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66041551568042840192468845 24765581838016065072175817)
              ·
                refine ⟨18574186378512048804131863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24765581838016065072175817 18574186378512048804131863)
                ·
                  refine ⟨27861279567768073206197795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18574186378512048804131863 27861279567768073206197795)
                  ·
                    refine ⟨41791919351652109809296693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27861279567768073206197795 41791919351652109809296693)
                    ·
                      refine ⟨3917992439217385294621565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41791919351652109809296693 3917992439217385294621565)
                      ·
                        rfl

theorem cell23_7630263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_7630263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630263 prefixEnd_7630263 := by exact prefixLift 7630263
  have htrace : WordTrace (prefixWord ++ tailWord_7630263) baseStart_7630263 baseEnd_7630263 := by
    simpa [prefixWord, tailWord_7630263, baseEnd_7630263] using wordTrace_append hprefix tailTrace_7630263
  have hstable : (prefixWord ++ tailWord_7630263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630263).length < 2 ^ (prefixWord ++ tailWord_7630263).sum := by decide
  have hdescent : baseEnd_7630263 < baseStart_7630263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630283 : List Nat := [1, 1, 1, 1, 3, 3, 6, 7]
def baseStart_7630283 : Nat := 118140960795 + 7630283 * 2 ^ 59
def prefixEnd_7630283 : Nat := 4983230072969 + 3 ^ 40 * 7630283 * 2
def baseEnd_7630283 : Nat := 145111211438165748754499

theorem tailTrace_7630283 : CollatzResearch.WordTrace tailWord_7630283 prefixEnd_7630283 145111211438165748754499 := by
  unfold tailWord_7630283
  simp only [CollatzResearch.WordTrace]
  refine ⟨278299284215795314432551503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185532856143863542955034335 278299284215795314432551503)
  ·
    refine ⟨417448926323692971648827255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278299284215795314432551503 417448926323692971648827255)
    ·
      refine ⟨626173389485539457473240883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417448926323692971648827255 626173389485539457473240883)
      ·
        refine ⟨939260084228309186209861325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626173389485539457473240883 939260084228309186209861325)
        ·
          refine ⟨352222531585615944828697997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939260084228309186209861325 352222531585615944828697997)
          ·
            refine ⟨132083449344605979310761749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352222531585615944828697997 132083449344605979310761749)
            ·
              refine ⟨6191411688028405280191957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132083449344605979310761749 6191411688028405280191957)
              ·
                refine ⟨145111211438165748754499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6191411688028405280191957 145111211438165748754499)
                ·
                  rfl

theorem cell23_7630283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 7].length) (baseStart_7630283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630283 prefixEnd_7630283 := by exact prefixLift 7630283
  have htrace : WordTrace (prefixWord ++ tailWord_7630283) baseStart_7630283 baseEnd_7630283 := by
    simpa [prefixWord, tailWord_7630283, baseEnd_7630283] using wordTrace_append hprefix tailTrace_7630283
  have hstable : (prefixWord ++ tailWord_7630283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630283).length < 2 ^ (prefixWord ++ tailWord_7630283).sum := by decide
  have hdescent : baseEnd_7630283 < baseStart_7630283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630353 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_7630353 : Nat := 118140960795 + 7630353 * 2 ^ 59
def prefixEnd_7630353 : Nat := 4983230072969 + 3 ^ 40 * 7630353 * 2
def baseEnd_7630353 : Nat := 3918038652476289942496151

theorem tailTrace_7630353 : CollatzResearch.WordTrace tailWord_7630353 prefixEnd_7630353 3918038652476289942496151 := by
  unfold tailWord_7630353
  simp only [CollatzResearch.WordTrace]
  refine ⟨278301837325541716387599713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185534558217027810925066475 278301837325541716387599713)
  ·
    refine ⟨208726377994156287290699785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278301837325541716387599713 208726377994156287290699785)
    ·
      refine ⟨156544783495617215468024839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208726377994156287290699785 156544783495617215468024839)
      ·
        refine ⟨234817175243425823202037259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156544783495617215468024839 234817175243425823202037259)
        ·
          refine ⟨352225762865138734803055889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234817175243425823202037259 352225762865138734803055889)
          ·
            refine ⟨264169322148854051102291917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352225762865138734803055889 264169322148854051102291917)
            ·
              refine ⟨99063495805820269163359469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264169322148854051102291917 99063495805820269163359469)
              ·
                refine ⟨37148810927182600936259801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99063495805820269163359469 37148810927182600936259801)
                ·
                  refine ⟨27861608195386950702194851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37148810927182600936259801 27861608195386950702194851)
                  ·
                    refine ⟨41792412293080426053292277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27861608195386950702194851 41792412293080426053292277)
                    ·
                      refine ⟨3918038652476289942496151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41792412293080426053292277 3918038652476289942496151)
                      ·
                        rfl

theorem cell23_7630353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_7630353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630353 prefixEnd_7630353 := by exact prefixLift 7630353
  have htrace : WordTrace (prefixWord ++ tailWord_7630353) baseStart_7630353 baseEnd_7630353 := by
    simpa [prefixWord, tailWord_7630353, baseEnd_7630353] using wordTrace_append hprefix tailTrace_7630353
  have hstable : (prefixWord ++ tailWord_7630353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630353).length < 2 ^ (prefixWord ++ tailWord_7630353).sum := by decide
  have hdescent : baseEnd_7630353 < baseStart_7630353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630367 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 4, 2, 2]
def baseStart_7630367 : Nat := 118140960795 + 7630367 * 2 ^ 59
def prefixEnd_7630367 : Nat := 4983230072969 + 3 ^ 40 * 7630367 * 2
def baseEnd_7630367 : Nat := 3918045841205452887721087

theorem tailTrace_7630367 : CollatzResearch.WordTrace tailWord_7630367 prefixEnd_7630367 3918045841205452887721087 := by
  unfold tailWord_7630367
  simp only [CollatzResearch.WordTrace]
  refine ⟨278302347947490996778609355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185534898631660664519072903 278302347947490996778609355)
  ·
    refine ⟨417453521921236495167914033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278302347947490996778609355 417453521921236495167914033)
    ·
      refine ⟨313090141440927371375935525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417453521921236495167914033 313090141440927371375935525)
      ·
        refine ⟨58704401520173882132987911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313090141440927371375935525 58704401520173882132987911)
        ·
          refine ⟨88056602280260823199481867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58704401520173882132987911 88056602280260823199481867)
          ·
            refine ⟨132084903420391234799222801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88056602280260823199481867 132084903420391234799222801)
            ·
              refine ⟨99063677565293426099417101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132084903420391234799222801 99063677565293426099417101)
              ·
                refine ⟨37148879086985034787281413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99063677565293426099417101 37148879086985034787281413)
                ·
                  refine ⟨6965414828809694022615265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37148879086985034787281413 6965414828809694022615265)
                  ·
                    refine ⟨5224061121607270516961449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6965414828809694022615265 5224061121607270516961449)
                    ·
                      refine ⟨3918045841205452887721087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224061121607270516961449 3918045841205452887721087)
                      ·
                        rfl

theorem cell23_7630367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_7630367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630367 prefixEnd_7630367 := by exact prefixLift 7630367
  have htrace : WordTrace (prefixWord ++ tailWord_7630367) baseStart_7630367 baseEnd_7630367 := by
    simpa [prefixWord, tailWord_7630367, baseEnd_7630367] using wordTrace_append hprefix tailTrace_7630367
  have hstable : (prefixWord ++ tailWord_7630367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630367).length < 2 ^ (prefixWord ++ tailWord_7630367).sum := by decide
  have hdescent : baseEnd_7630367 < baseStart_7630367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630370 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_7630370 : Nat := 118140960795 + 7630370 * 2 ^ 59
def prefixEnd_7630370 : Nat := 4983230072969 + 3 ^ 40 * 7630370 * 2
def baseEnd_7630370 : Nat := 3918047381647416375983573

theorem tailTrace_7630370 : CollatzResearch.WordTrace tailWord_7630370 prefixEnd_7630370 3918047381647416375983573 := by
  unfold tailWord_7630370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69575614341620032072742141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185534971577653418860645709 69575614341620032072742141)
  ·
    refine ⟨26090855378107512027278303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69575614341620032072742141 26090855378107512027278303)
    ·
      refine ⟨39136283067161268040917455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26090855378107512027278303 39136283067161268040917455)
      ·
        refine ⟨58704424600741902061376183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39136283067161268040917455 58704424600741902061376183)
        ·
          refine ⟨88056636901112853092064275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58704424600741902061376183 88056636901112853092064275)
          ·
            refine ⟨132084955351669279638096413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88056636901112853092064275 132084955351669279638096413)
            ·
              refine ⟨49531858256875979864286155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132084955351669279638096413 49531858256875979864286155)
              ·
                refine ⟨74297787385313969796429233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49531858256875979864286155 74297787385313969796429233)
                ·
                  refine ⟨55723340538985477347321925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74297787385313969796429233 55723340538985477347321925)
                  ·
                    refine ⟨10448126351059777002622861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55723340538985477347321925 10448126351059777002622861)
                    ·
                      refine ⟨3918047381647416375983573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10448126351059777002622861 3918047381647416375983573)
                      ·
                        rfl

theorem cell23_7630370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_7630370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630370 prefixEnd_7630370 := by exact prefixLift 7630370
  have htrace : WordTrace (prefixWord ++ tailWord_7630370) baseStart_7630370 baseEnd_7630370 := by
    simpa [prefixWord, tailWord_7630370, baseEnd_7630370] using wordTrace_append hprefix tailTrace_7630370
  have hstable : (prefixWord ++ tailWord_7630370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630370).length < 2 ^ (prefixWord ++ tailWord_7630370).sum := by decide
  have hdescent : baseEnd_7630370 < baseStart_7630370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630373 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 7]
def baseStart_7630373 : Nat := 118140960795 + 7630373 * 2 ^ 59
def prefixEnd_7630373 : Nat := 4983230072969 + 3 ^ 40 * 7630373 * 2
def baseEnd_7630373 : Nat := 435338769121042207138451

theorem tailTrace_7630373 : CollatzResearch.WordTrace tailWord_7630373 prefixEnd_7630373 435338769121042207138451 := by
  unfold tailWord_7630373
  simp only [CollatzResearch.WordTrace]
  refine ⟨278302566785469259803327773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185535044523646173202218515 278302566785469259803327773)
  ·
    refine ⟨104363462544550972426247915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278302566785469259803327773 104363462544550972426247915)
    ·
      refine ⟨156545193816826458639371873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104363462544550972426247915 156545193816826458639371873)
      ·
        refine ⟨117408895362619843979528905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156545193816826458639371873 117408895362619843979528905)
        ·
          refine ⟨88056671521964882984646679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117408895362619843979528905 88056671521964882984646679)
          ·
            refine ⟨132085007282947324476970019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88056671521964882984646679 132085007282947324476970019)
            ·
              refine ⟨198127510924420986715455029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132085007282947324476970019 198127510924420986715455029)
              ·
                refine ⟨18574454149164467504573909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198127510924420986715455029 18574454149164467504573909)
                ·
                  refine ⟨435338769121042207138451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18574454149164467504573909 435338769121042207138451)
                  ·
                    rfl

theorem cell23_7630373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_7630373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630373 prefixEnd_7630373 := by exact prefixLift 7630373
  have htrace : WordTrace (prefixWord ++ tailWord_7630373) baseStart_7630373 baseEnd_7630373 := by
    simpa [prefixWord, tailWord_7630373, baseEnd_7630373] using wordTrace_append hprefix tailTrace_7630373
  have hstable : (prefixWord ++ tailWord_7630373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630373).length < 2 ^ (prefixWord ++ tailWord_7630373).sum := by decide
  have hdescent : baseEnd_7630373 < baseStart_7630373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630420 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_7630420 : Nat := 118140960795 + 7630420 * 2 ^ 59
def prefixEnd_7630420 : Nat := 4983230072969 + 3 ^ 40 * 7630420 * 2
def baseEnd_7630420 : Nat := 1306024351893380393452781

theorem tailTrace_7630420 : CollatzResearch.WordTrace tailWord_7630420 prefixEnd_7630420 1306024351893380393452781 := by
  unfold tailWord_7630420
  simp only [CollatzResearch.WordTrace]
  refine ⟨139152140508149493415144357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185536187344199324553525809 139152140508149493415144357)
  ·
    refine ⟨26091026345278030015339567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139152140508149493415144357 26091026345278030015339567)
    ·
      refine ⟨39136539517917045023009351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26091026345278030015339567 39136539517917045023009351)
      ·
        refine ⟨58704809276875567534514027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39136539517917045023009351 58704809276875567534514027)
        ·
          refine ⟨88057213915313351301771041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58704809276875567534514027 88057213915313351301771041)
          ·
            refine ⟨66042910436485013476328281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88057213915313351301771041 66042910436485013476328281)
            ·
              refine ⟨49532182827363760107246211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66042910436485013476328281 49532182827363760107246211)
              ·
                refine ⟨74298274241045640160869317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49532182827363760107246211 74298274241045640160869317)
                ·
                  refine ⟨13930926420196057530162997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74298274241045640160869317 13930926420196057530162997)
                  ·
                    refine ⟨1306024351893380393452781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13930926420196057530162997 1306024351893380393452781)
                    ·
                      rfl

theorem cell23_7630420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_7630420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630420 prefixEnd_7630420 := by exact prefixLift 7630420
  have htrace : WordTrace (prefixWord ++ tailWord_7630420) baseStart_7630420 baseEnd_7630420 := by
    simpa [prefixWord, tailWord_7630420, baseEnd_7630420] using wordTrace_append hprefix tailTrace_7630420
  have hstable : (prefixWord ++ tailWord_7630420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630420).length < 2 ^ (prefixWord ++ tailWord_7630420).sum := by decide
  have hdescent : baseEnd_7630420 < baseStart_7630420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630443 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_7630443 : Nat := 118140960795 + 7630443 * 2 ^ 59
def prefixEnd_7630443 : Nat := 4983230072969 + 3 ^ 40 * 7630443 * 2
def baseEnd_7630443 : Nat := 3918084865735194590370737

theorem tailTrace_7630443 : CollatzResearch.WordTrace tailWord_7630443 prefixEnd_7630443 3918084865735194590370737 := by
  unfold tailWord_7630443
  simp only [CollatzResearch.WordTrace]
  refine ⟨278305119895215661758375983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185536746596810441172250655 278305119895215661758375983)
  ·
    refine ⟨417457679842823492637563975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278305119895215661758375983 417457679842823492637563975)
    ·
      refine ⟨626186519764235238956345963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417457679842823492637563975 626186519764235238956345963)
      ·
        refine ⟨939279779646352858434518945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626186519764235238956345963 939279779646352858434518945)
        ·
          refine ⟨704459834734764643825889209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 939279779646352858434518945 704459834734764643825889209)
          ·
            refine ⟨528344876051073482869416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704459834734764643825889209 528344876051073482869416907)
            ·
              refine ⟨792517314076610224304125361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528344876051073482869416907 792517314076610224304125361)
              ·
                refine ⟨594387985557457668228094021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792517314076610224304125361 594387985557457668228094021)
                ·
                  refine ⟨111447747292023312792767629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594387985557457668228094021 111447747292023312792767629)
                  ·
                    refine ⟨41792905234508742297287861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111447747292023312792767629 41792905234508742297287861)
                    ·
                      refine ⟨3918084865735194590370737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41792905234508742297287861 3918084865735194590370737)
                      ·
                        rfl

theorem cell23_7630443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_7630443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630443 prefixEnd_7630443 := by exact prefixLift 7630443
  have htrace : WordTrace (prefixWord ++ tailWord_7630443) baseStart_7630443 baseEnd_7630443 := by
    simpa [prefixWord, tailWord_7630443, baseEnd_7630443] using wordTrace_append hprefix tailTrace_7630443
  have hstable : (prefixWord ++ tailWord_7630443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630443).length < 2 ^ (prefixWord ++ tailWord_7630443).sum := by decide
  have hdescent : baseEnd_7630443 < baseStart_7630443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630497 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 6]
def baseStart_7630497 : Nat := 118140960795 + 7630497 * 2 ^ 59
def prefixEnd_7630497 : Nat := 4983230072969 + 3 ^ 40 * 7630497 * 2
def baseEnd_7630497 : Nat := 435345843743393042121721

theorem tailTrace_7630497 : CollatzResearch.WordTrace tailWord_7630497 prefixEnd_7630497 435345843743393042121721 := by
  unfold tailWord_7630497
  simp only [CollatzResearch.WordTrace]
  refine ⟨278307089437020028980841745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185538059624680019320561163 278307089437020028980841745)
  ·
    refine ⟨208730317077765021735631309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278307089437020028980841745 208730317077765021735631309)
    ·
      refine ⟨78273868904161883150861741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208730317077765021735631309 78273868904161883150861741)
      ·
        refine ⟨29352700839060706181573153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78273868904161883150861741 29352700839060706181573153)
        ·
          refine ⟨22014525629295529636179865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29352700839060706181573153 22014525629295529636179865)
          ·
            refine ⟨16510894221971647227134899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22014525629295529636179865 16510894221971647227134899)
            ·
              refine ⟨24766341332957470840702349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16510894221971647227134899 24766341332957470840702349)
              ·
                refine ⟨9287377999859051565263381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24766341332957470840702349 9287377999859051565263381)
                ·
                  refine ⟨435345843743393042121721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9287377999859051565263381 435345843743393042121721)
                  ·
                    rfl

theorem cell23_7630497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_7630497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630497 prefixEnd_7630497 := by exact prefixLift 7630497
  have htrace : WordTrace (prefixWord ++ tailWord_7630497) baseStart_7630497 baseEnd_7630497 := by
    simpa [prefixWord, tailWord_7630497, baseEnd_7630497] using wordTrace_append hprefix tailTrace_7630497
  have hstable : (prefixWord ++ tailWord_7630497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630497).length < 2 ^ (prefixWord ++ tailWord_7630497).sum := by decide
  have hdescent : baseEnd_7630497 < baseStart_7630497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630560 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_7630560 : Nat := 118140960795 + 7630560 * 2 ^ 59
def prefixEnd_7630560 : Nat := 4983230072969 + 3 ^ 40 * 7630560 * 2
def baseEnd_7630560 : Nat := 3918144942971770632607699

theorem tailTrace_7630560 : CollatzResearch.WordTrace tailWord_7630560 prefixEnd_7630560 3918144942971770632607699 := by
  unfold tailWord_7630560
  simp only [CollatzResearch.WordTrace]
  refine ⟨139154693617895895370192567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185539591490527860493590089 139154693617895895370192567)
  ·
    refine ⟨208732040426843843055288851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139154693617895895370192567 208732040426843843055288851)
    ·
      refine ⟨313098060640265764582933277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208732040426843843055288851 313098060640265764582933277)
      ·
        refine ⟨117411772740099661718599979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313098060640265764582933277 117411772740099661718599979)
        ·
          refine ⟨176117659110149492577899969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117411772740099661718599979 176117659110149492577899969)
          ·
            refine ⟨132088244332612119433424977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176117659110149492577899969 132088244332612119433424977)
            ·
              refine ⟨99066183249459089575068733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132088244332612119433424977 99066183249459089575068733)
              ·
                refine ⟨37149818718547158590650775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99066183249459089575068733 37149818718547158590650775)
                ·
                  refine ⟨55724728077820737885976163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37149818718547158590650775 55724728077820737885976163)
                  ·
                    refine ⟨83587092116731106828964245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55724728077820737885976163 83587092116731106828964245)
                    ·
                      refine ⟨3918144942971770632607699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83587092116731106828964245 3918144942971770632607699)
                      ·
                        rfl

theorem cell23_7630560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_7630560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630560 prefixEnd_7630560 := by exact prefixLift 7630560
  have htrace : WordTrace (prefixWord ++ tailWord_7630560) baseStart_7630560 baseEnd_7630560 := by
    simpa [prefixWord, tailWord_7630560, baseEnd_7630560] using wordTrace_append hprefix tailTrace_7630560
  have hstable : (prefixWord ++ tailWord_7630560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630560).length < 2 ^ (prefixWord ++ tailWord_7630560).sum := by decide
  have hdescent : baseEnd_7630560 < baseStart_7630560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630570 : List Nat := [3, 1, 3, 1, 1, 1, 2, 11]
def baseStart_7630570 : Nat := 118140960795 + 7630570 * 2 ^ 59
def prefixEnd_7630570 : Nat := 4983230072969 + 3 ^ 40 * 7630570 * 2
def baseEnd_7630570 : Nat := 145116669547345021980839

theorem tailTrace_7630570 : CollatzResearch.WordTrace tailWord_7630570 prefixEnd_7630570 145116669547345021980839 := by
  unfold tailWord_7630570
  simp only [CollatzResearch.WordTrace]
  refine ⟨69577437991438890612062291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185539834643837041632166109 69577437991438890612062291)
  ·
    refine ⟨104366156987158335918093437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69577437991438890612062291 104366156987158335918093437)
    ·
      refine ⟨39137308870184375969285039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104366156987158335918093437 39137308870184375969285039)
      ·
        refine ⟨58705963305276563953927559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39137308870184375969285039 58705963305276563953927559)
        ·
          refine ⟨88058944957914845930891339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58705963305276563953927559 88058944957914845930891339)
          ·
            refine ⟨132088417436872268896337009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88058944957914845930891339 132088417436872268896337009)
            ·
              refine ⟨99066313077654201672252757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132088417436872268896337009 99066313077654201672252757)
              ·
                refine ⟨145116669547345021980839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99066313077654201672252757 145116669547345021980839)
                ·
                  rfl

theorem cell23_7630570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_7630570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630570 prefixEnd_7630570 := by exact prefixLift 7630570
  have htrace : WordTrace (prefixWord ++ tailWord_7630570) baseStart_7630570 baseEnd_7630570 := by
    simpa [prefixWord, tailWord_7630570, baseEnd_7630570] using wordTrace_append hprefix tailTrace_7630570
  have hstable : (prefixWord ++ tailWord_7630570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630570).length < 2 ^ (prefixWord ++ tailWord_7630570).sum := by decide
  have hdescent : baseEnd_7630570 < baseStart_7630570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630577 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_7630577 : Nat := 118140960795 + 7630577 * 2 ^ 59
def prefixEnd_7630577 : Nat := 4983230072969 + 3 ^ 40 * 7630577 * 2
def baseEnd_7630577 : Nat := 3918153672142897066095121

theorem tailTrace_7630577 : CollatzResearch.WordTrace tailWord_7630577 prefixEnd_7630577 3918153672142897066095121 := by
  unfold tailWord_7630577
  simp only [CollatzResearch.WordTrace]
  refine ⟨278310007276730202643753985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185540004851153468429169323 278310007276730202643753985)
  ·
    refine ⟨208732505457547651982815489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278310007276730202643753985 208732505457547651982815489)
    ·
      refine ⟨156549379093160738987111617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208732505457547651982815489 156549379093160738987111617)
      ·
        refine ⟨117412034319870554240333713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156549379093160738987111617 117412034319870554240333713)
        ·
          refine ⟨88059025739902915680250285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117412034319870554240333713 88059025739902915680250285)
          ·
            refine ⟨33022134652463593380093857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88059025739902915680250285 33022134652463593380093857)
            ·
              refine ⟨24766600989347695035070393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33022134652463593380093857 24766600989347695035070393)
              ·
                refine ⟨18574950742010771276302795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24766600989347695035070393 18574950742010771276302795)
                ·
                  refine ⟨27862426113016156914454193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18574950742010771276302795 27862426113016156914454193)
                  ·
                    refine ⟨20896819584762117685840645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27862426113016156914454193 20896819584762117685840645)
                    ·
                      refine ⟨3918153672142897066095121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20896819584762117685840645 3918153672142897066095121)
                      ·
                        rfl

theorem cell23_7630577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_7630577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630577 prefixEnd_7630577 := by exact prefixLift 7630577
  have htrace : WordTrace (prefixWord ++ tailWord_7630577) baseStart_7630577 baseEnd_7630577 := by
    simpa [prefixWord, tailWord_7630577, baseEnd_7630577] using wordTrace_append hprefix tailTrace_7630577
  have hstable : (prefixWord ++ tailWord_7630577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630577).length < 2 ^ (prefixWord ++ tailWord_7630577).sum := by decide
  have hdescent : baseEnd_7630577 < baseStart_7630577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630607 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 7, 2]
def baseStart_7630607 : Nat := 118140960795 + 7630607 * 2 ^ 59
def prefixEnd_7630607 : Nat := 4983230072969 + 3 ^ 40 * 7630607 * 2
def baseEnd_7630607 : Nat := 3918169076562531948719983

theorem tailTrace_7630607 : CollatzResearch.WordTrace tailWord_7630607 prefixEnd_7630607 3918169076562531948719983 := by
  unfold tailWord_7630607
  simp only [CollatzResearch.WordTrace]
  refine ⟨278311101466621517767346075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185540734311081011844897383 278311101466621517767346075)
  ·
    refine ⟨417466652199932276651019113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278311101466621517767346075 417466652199932276651019113)
    ·
      refine ⟨313099989149949207488264335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417466652199932276651019113 313099989149949207488264335)
      ·
        refine ⟨469649983724923811232396503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313099989149949207488264335 469649983724923811232396503)
        ·
          refine ⟨704474975587385716848594755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469649983724923811232396503 704474975587385716848594755)
          ·
            refine ⟨1056712463381078575272892133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704474975587385716848594755 1056712463381078575272892133)
            ·
              refine ⟨198133586883952232863667275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1056712463381078575272892133 198133586883952232863667275)
              ·
                refine ⟨297200380325928349295500913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198133586883952232863667275 297200380325928349295500913)
                ·
                  refine ⟨222900285244446261971625685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297200380325928349295500913 222900285244446261971625685)
                  ·
                    refine ⟨5224225435416709264959977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222900285244446261971625685 5224225435416709264959977)
                    ·
                      refine ⟨3918169076562531948719983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224225435416709264959977 3918169076562531948719983)
                      ·
                        rfl

theorem cell23_7630607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7, 2].length) (baseStart_7630607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630607 prefixEnd_7630607 := by exact prefixLift 7630607
  have htrace : WordTrace (prefixWord ++ tailWord_7630607) baseStart_7630607 baseEnd_7630607 := by
    simpa [prefixWord, tailWord_7630607, baseEnd_7630607] using wordTrace_append hprefix tailTrace_7630607
  have hstable : (prefixWord ++ tailWord_7630607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630607).length < 2 ^ (prefixWord ++ tailWord_7630607).sum := by decide
  have hdescent : baseEnd_7630607 < baseStart_7630607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630641 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_7630641 : Nat := 118140960795 + 7630641 * 2 ^ 59
def prefixEnd_7630641 : Nat := 4983230072969 + 3 ^ 40 * 7630641 * 2
def baseEnd_7630641 : Nat := 3918186534904784815694827

theorem tailTrace_7630641 : CollatzResearch.WordTrace tailWord_7630641 prefixEnd_7630641 3918186534904784815694827 := by
  unfold tailWord_7630641
  simp only [CollatzResearch.WordTrace]
  refine ⟨278312341548498341574083777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185541561032332227716055851 278312341548498341574083777)
  ·
    refine ⟨208734256161373756180562833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278312341548498341574083777 208734256161373756180562833)
    ·
      refine ⟨156550692121030317135422125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208734256161373756180562833 156550692121030317135422125)
      ·
        refine ⟨58706509545386368925783297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156550692121030317135422125 58706509545386368925783297)
        ·
          refine ⟨44029882159039776694337473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58706509545386368925783297 44029882159039776694337473)
          ·
            refine ⟨33022411619279832520753105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44029882159039776694337473 33022411619279832520753105)
            ·
              refine ⟨24766808714459874390564829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33022411619279832520753105 24766808714459874390564829)
              ·
                refine ⟨9287553267922452896461811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24766808714459874390564829 9287553267922452896461811)
                ·
                  refine ⟨13931329901883679344692717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9287553267922452896461811 13931329901883679344692717)
                  ·
                    refine ⟨5224248713206379754259769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13931329901883679344692717 5224248713206379754259769)
                    ·
                      refine ⟨3918186534904784815694827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224248713206379754259769 3918186534904784815694827)
                      ·
                        rfl

theorem cell23_7630641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_7630641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630641 prefixEnd_7630641 := by exact prefixLift 7630641
  have htrace : WordTrace (prefixWord ++ tailWord_7630641) baseStart_7630641 baseEnd_7630641 := by
    simpa [prefixWord, tailWord_7630641, baseEnd_7630641] using wordTrace_append hprefix tailTrace_7630641
  have hstable : (prefixWord ++ tailWord_7630641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630641).length < 2 ^ (prefixWord ++ tailWord_7630641).sum := by decide
  have hdescent : baseEnd_7630641 < baseStart_7630641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630714 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_7630714 : Nat := 118140960795 + 7630714 * 2 ^ 59
def prefixEnd_7630714 : Nat := 4983230072969 + 3 ^ 40 * 7630714 * 2
def baseEnd_7630714 : Nat := 3918224018992563030081991

theorem tailTrace_7630714 : CollatzResearch.WordTrace tailWord_7630714 prefixEnd_7630714 3918224018992563030081991 := by
  unfold tailWord_7630714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69578751019308468760372799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185543336051489250027660797 69578751019308468760372799)
  ·
    refine ⟨104368126528962703140559199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69578751019308468760372799 104368126528962703140559199)
    ·
      refine ⟨156552189793444054710838799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104368126528962703140559199 156552189793444054710838799)
      ·
        refine ⟨234828284690166082066258199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156552189793444054710838799 234828284690166082066258199)
        ·
          refine ⟨352242427035249123099387299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234828284690166082066258199 352242427035249123099387299)
          ·
            refine ⟨528363640552873684649080949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352242427035249123099387299 528363640552873684649080949)
            ·
              refine ⟨49534091301831907935851339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528363640552873684649080949 49534091301831907935851339)
              ·
                refine ⟨74301136952747861903777009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49534091301831907935851339 74301136952747861903777009)
                ·
                  refine ⟨55725852714560896427832757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74301136952747861903777009 55725852714560896427832757)
                  ·
                    refine ⟨5224298691990084040109321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55725852714560896427832757 5224298691990084040109321)
                    ·
                      refine ⟨3918224018992563030081991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224298691990084040109321 3918224018992563030081991)
                      ·
                        rfl

theorem cell23_7630714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_7630714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630714 prefixEnd_7630714 := by exact prefixLift 7630714
  have htrace : WordTrace (prefixWord ++ tailWord_7630714) baseStart_7630714 baseEnd_7630714 := by
    simpa [prefixWord, tailWord_7630714, baseEnd_7630714] using wordTrace_append hprefix tailTrace_7630714
  have hstable : (prefixWord ++ tailWord_7630714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630714).length < 2 ^ (prefixWord ++ tailWord_7630714).sum := by decide
  have hdescent : baseEnd_7630714 < baseStart_7630714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630757 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7630757 : Nat := 118140960795 + 7630757 * 2 ^ 59
def prefixEnd_7630757 : Nat := 4983230072969 + 3 ^ 40 * 7630757 * 2
def baseEnd_7630757 : Nat := 3918246098660706361844293

theorem tailTrace_7630757 : CollatzResearch.WordTrace tailWord_7630757 prefixEnd_7630757 3918246098660706361844293 := by
  unfold tailWord_7630757
  simp only [CollatzResearch.WordTrace]
  refine ⟨278316572416078093385306525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185544381610718728923537683 278316572416078093385306525)
  ·
    refine ⟨104368714656029285019489947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278316572416078093385306525 104368714656029285019489947)
    ·
      refine ⟨156553071984043927529234921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104368714656029285019489947 156553071984043927529234921)
      ·
        refine ⟨117414803988032945646926191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156553071984043927529234921 117414803988032945646926191)
        ·
          refine ⟨176122205982049418470389287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117414803988032945646926191 176122205982049418470389287)
          ·
            refine ⟨264183308973074127705583931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176122205982049418470389287 264183308973074127705583931)
            ·
              refine ⟨396274963459611191558375897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264183308973074127705583931 396274963459611191558375897)
              ·
                refine ⟨297206222594708393668781923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396274963459611191558375897 297206222594708393668781923)
                ·
                  refine ⟨445809333892062590503172885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297206222594708393668781923 445809333892062590503172885)
                  ·
                    refine ⟨20897312526190433929836229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 445809333892062590503172885 20897312526190433929836229)
                    ·
                      refine ⟨3918246098660706361844293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20897312526190433929836229 3918246098660706361844293)
                      ·
                        rfl

theorem cell23_7630757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7630757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630757 prefixEnd_7630757 := by exact prefixLift 7630757
  have htrace : WordTrace (prefixWord ++ tailWord_7630757) baseStart_7630757 baseEnd_7630757 := by
    simpa [prefixWord, tailWord_7630757, baseEnd_7630757] using wordTrace_append hprefix tailTrace_7630757
  have hstable : (prefixWord ++ tailWord_7630757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630757).length < 2 ^ (prefixWord ++ tailWord_7630757).sum := by decide
  have hdescent : baseEnd_7630757 < baseStart_7630757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630767 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 8]
def baseStart_7630767 : Nat := 118140960795 + 7630767 * 2 ^ 59
def prefixEnd_7630767 : Nat := 4983230072969 + 3 ^ 40 * 7630767 * 2
def baseEnd_7630767 : Nat := 435361248163027924746583

theorem tailTrace_7630767 : CollatzResearch.WordTrace tailWord_7630767 prefixEnd_7630767 435361248163027924746583 := by
  unfold tailWord_7630767
  simp only [CollatzResearch.WordTrace]
  refine ⟨278316937146041865093170555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185544624764027910062113703 278316937146041865093170555)
  ·
    refine ⟨417475405719062797639755833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278316937146041865093170555 417475405719062797639755833)
    ·
      refine ⟨313106554289297098229816875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417475405719062797639755833 313106554289297098229816875)
      ·
        refine ⟨469659831433945647344725313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313106554289297098229816875 469659831433945647344725313)
        ·
          refine ⟨352244873575459235508543985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469659831433945647344725313 352244873575459235508543985)
          ·
            refine ⟨264183655181594426631407989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352244873575459235508543985 264183655181594426631407989)
            ·
              refine ⟨24767217673274477496694499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264183655181594426631407989 24767217673274477496694499)
              ·
                refine ⟨37150826509911716245041749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24767217673274477496694499 37150826509911716245041749)
                ·
                  refine ⟨435361248163027924746583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37150826509911716245041749 435361248163027924746583)
                  ·
                    rfl

theorem cell23_7630767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 8].length) (baseStart_7630767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630767 prefixEnd_7630767 := by exact prefixLift 7630767
  have htrace : WordTrace (prefixWord ++ tailWord_7630767) baseStart_7630767 baseEnd_7630767 := by
    simpa [prefixWord, tailWord_7630767, baseEnd_7630767] using wordTrace_append hprefix tailTrace_7630767
  have hstable : (prefixWord ++ tailWord_7630767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630767).length < 2 ^ (prefixWord ++ tailWord_7630767).sum := by decide
  have hdescent : baseEnd_7630767 < baseStart_7630767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630771 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 1, 4]
def baseStart_7630771 : Nat := 118140960795 + 7630771 * 2 ^ 59
def prefixEnd_7630771 : Nat := 4983230072969 + 3 ^ 40 * 7630771 * 2
def baseEnd_7630771 : Nat := 1306084429129956435689743

theorem tailTrace_7630771 : CollatzResearch.WordTrace tailWord_7630771 prefixEnd_7630771 1306084429129956435689743 := by
  unfold tailWord_7630771
  simp only [CollatzResearch.WordTrace]
  refine ⟨278317083038027373776316167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185544722025351582517544111 278317083038027373776316167)
  ·
    refine ⟨417475624557041060664474251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278317083038027373776316167 417475624557041060664474251)
    ·
      refine ⟨626213436835561590996711377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417475624557041060664474251 626213436835561590996711377)
      ·
        refine ⟨469660077626671193247533533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626213436835561590996711377 469660077626671193247533533)
        ·
          refine ⟨176122529110001697467825075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469660077626671193247533533 176122529110001697467825075)
          ·
            refine ⟨264183793665002546201737613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176122529110001697467825075 264183793665002546201737613)
            ·
              refine ⟨99068922624375954825651605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264183793665002546201737613 99068922624375954825651605)
              ·
                refine ⟨4643855748017622882452419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99068922624375954825651605 4643855748017622882452419)
                ·
                  refine ⟨6965783622026434323678629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643855748017622882452419 6965783622026434323678629)
                  ·
                    refine ⟨1306084429129956435689743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965783622026434323678629 1306084429129956435689743)
                    ·
                      rfl

theorem cell23_7630771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 4].length) (baseStart_7630771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630771 prefixEnd_7630771 := by exact prefixLift 7630771
  have htrace : WordTrace (prefixWord ++ tailWord_7630771) baseStart_7630771 baseEnd_7630771 := by
    simpa [prefixWord, tailWord_7630771, baseEnd_7630771] using wordTrace_append hprefix tailTrace_7630771
  have hstable : (prefixWord ++ tailWord_7630771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630771).length < 2 ^ (prefixWord ++ tailWord_7630771).sum := by decide
  have hdescent : baseEnd_7630771 < baseStart_7630771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630805 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_7630805 : Nat := 118140960795 + 7630805 * 2 ^ 59
def prefixEnd_7630805 : Nat := 4983230072969 + 3 ^ 40 * 7630805 * 2
def baseEnd_7630805 : Nat := 1306090248577374058014691

theorem tailTrace_7630805 : CollatzResearch.WordTrace tailWord_7630805 prefixEnd_7630805 1306090248577374058014691 := by
  unfold tailWord_7630805
  simp only [CollatzResearch.WordTrace]
  refine ⟨278318323119904197583053869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185545548746602798388702579 278318323119904197583053869)
  ·
    refine ⟨104369371169964074093645201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278318323119904197583053869 104369371169964074093645201)
    ·
      refine ⟨78277028377473055570233901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104369371169964074093645201 78277028377473055570233901)
      ·
        refine ⟨29353885641552395838837713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78277028377473055570233901 29353885641552395838837713)
        ·
          refine ⟨22015414231164296879128285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29353885641552395838837713 22015414231164296879128285)
          ·
            refine ⟨8255780336686611329673107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22015414231164296879128285 8255780336686611329673107)
            ·
              refine ⟨12383670505029916994509661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8255780336686611329673107 12383670505029916994509661)
              ·
                refine ⟨4643876439386218872941123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12383670505029916994509661 4643876439386218872941123)
                ·
                  refine ⟨6965814659079328309411685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643876439386218872941123 6965814659079328309411685)
                  ·
                    refine ⟨1306090248577374058014691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965814659079328309411685 1306090248577374058014691)
                    ·
                      rfl

theorem cell23_7630805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_7630805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630805 prefixEnd_7630805 := by exact prefixLift 7630805
  have htrace : WordTrace (prefixWord ++ tailWord_7630805) baseStart_7630805 baseEnd_7630805 := by
    simpa [prefixWord, tailWord_7630805, baseEnd_7630805] using wordTrace_append hprefix tailTrace_7630805
  have hstable : (prefixWord ++ tailWord_7630805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630805).length < 2 ^ (prefixWord ++ tailWord_7630805).sum := by decide
  have hdescent : baseEnd_7630805 < baseStart_7630805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630828 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 1, 1, 3]
def baseStart_7630828 : Nat := 118140960795 + 7630828 * 2 ^ 59
def prefixEnd_7630828 : Nat := 4983230072969 + 3 ^ 40 * 7630828 * 2
def baseEnd_7630828 : Nat := 3918282555787175584056467

theorem tailTrace_7630828 : CollatzResearch.WordTrace tailWord_7630828 prefixEnd_7630828 3918282555787175584056467 := by
  unfold tailWord_7630828
  simp only [CollatzResearch.WordTrace]
  refine ⟨139159580999410436255570569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185546107999213915007427425 139159580999410436255570569)
  ·
    refine ⟨104369685749557827191677927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139159580999410436255570569 104369685749557827191677927)
    ·
      refine ⟨156554528624336740787516891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104369685749557827191677927 156554528624336740787516891)
      ·
        refine ⟨234831792936505111181275337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156554528624336740787516891 234831792936505111181275337)
        ·
          refine ⟨176123844702378833385956503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234831792936505111181275337 176123844702378833385956503)
          ·
            refine ⟨264185767053568250078934755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176123844702378833385956503 264185767053568250078934755)
            ·
              refine ⟨396278650580352375118402133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264185767053568250078934755 396278650580352375118402133)
              ·
                refine ⟨4643890436488504395918775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 396278650580352375118402133 4643890436488504395918775)
                ·
                  refine ⟨6965835654732756593878163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643890436488504395918775 6965835654732756593878163)
                  ·
                    refine ⟨10448753482099134890817245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6965835654732756593878163 10448753482099134890817245)
                    ·
                      refine ⟨3918282555787175584056467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10448753482099134890817245 3918282555787175584056467)
                      ·
                        rfl

theorem cell23_7630828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_7630828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630828 prefixEnd_7630828 := by exact prefixLift 7630828
  have htrace : WordTrace (prefixWord ++ tailWord_7630828) baseStart_7630828 baseEnd_7630828 := by
    simpa [prefixWord, tailWord_7630828, baseEnd_7630828] using wordTrace_append hprefix tailTrace_7630828
  have hstable : (prefixWord ++ tailWord_7630828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630828).length < 2 ^ (prefixWord ++ tailWord_7630828).sum := by decide
  have hdescent : baseEnd_7630828 < baseStart_7630828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630844 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_7630844 : Nat := 118140960795 + 7630844 * 2 ^ 59
def prefixEnd_7630844 : Nat := 4983230072969 + 3 ^ 40 * 7630844 * 2
def baseEnd_7630844 : Nat := 1306096923825882507152131

theorem tailTrace_7630844 : CollatzResearch.WordTrace tailWord_7630844 prefixEnd_7630844 1306096923825882507152131 := by
  unfold tailWord_7630844
  simp only [CollatzResearch.WordTrace]
  refine ⟨139159872783381453621861793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185546497044508604829149057 139159872783381453621861793)
  ·
    refine ⟨104369904587536090216396345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139159872783381453621861793 104369904587536090216396345)
    ·
      refine ⟨78277428440652067662297259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104369904587536090216396345 78277428440652067662297259)
      ·
        refine ⟨117416142660978101493445889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78277428440652067662297259 117416142660978101493445889)
        ·
          refine ⟨88062106995733576120084417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117416142660978101493445889 88062106995733576120084417)
          ·
            refine ⟨66046580246800182090063313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88062106995733576120084417 66046580246800182090063313)
            ·
              refine ⟨49534935185100136567547485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66046580246800182090063313 49534935185100136567547485)
              ·
                refine ⟨18575600694412551212830307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49534935185100136567547485 18575600694412551212830307)
                ·
                  refine ⟨27863401041618826819245461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18575600694412551212830307 27863401041618826819245461)
                  ·
                    refine ⟨1306096923825882507152131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27863401041618826819245461 1306096923825882507152131)
                    ·
                      rfl

theorem cell23_7630844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_7630844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630844 prefixEnd_7630844 := by exact prefixLift 7630844
  have htrace : WordTrace (prefixWord ++ tailWord_7630844) baseStart_7630844 baseEnd_7630844 := by
    simpa [prefixWord, tailWord_7630844, baseEnd_7630844] using wordTrace_append hprefix tailTrace_7630844
  have hstable : (prefixWord ++ tailWord_7630844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630844).length < 2 ^ (prefixWord ++ tailWord_7630844).sum := by decide
  have hdescent : baseEnd_7630844 < baseStart_7630844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630864 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_7630864 : Nat := 118140960795 + 7630864 * 2 ^ 59
def prefixEnd_7630864 : Nat := 4983230072969 + 3 ^ 40 * 7630864 * 2
def baseEnd_7630864 : Nat := 3918301041090737443206301

theorem tailTrace_7630864 : CollatzResearch.WordTrace tailWord_7630864 prefixEnd_7630864 3918301041090737443206301 := by
  unfold tailWord_7630864
  simp only [CollatzResearch.WordTrace]
  refine ⟨139160237513345225329725823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185546983351126967106301097 139160237513345225329725823)
  ·
    refine ⟨208740356270017837994588735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139160237513345225329725823 208740356270017837994588735)
    ·
      refine ⟨313110534405026756991883103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208740356270017837994588735 313110534405026756991883103)
      ·
        refine ⟨469665801607540135487824655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313110534405026756991883103 469665801607540135487824655)
        ·
          refine ⟨704498702411310203231736983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469665801607540135487824655 704498702411310203231736983)
          ·
            refine ⟨1056748053616965304847605475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704498702411310203231736983 1056748053616965304847605475)
            ·
              refine ⟨1585122080425447957271408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056748053616965304847605475 1585122080425447957271408213)
              ·
                refine ⟨18575649379985718249274315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1585122080425447957271408213 18575649379985718249274315)
                ·
                  refine ⟨27863474069978577373911473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18575649379985718249274315 27863474069978577373911473)
                  ·
                    refine ⟨20897605552483933030433605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27863474069978577373911473 20897605552483933030433605)
                    ·
                      refine ⟨3918301041090737443206301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20897605552483933030433605 3918301041090737443206301)
                      ·
                        rfl

theorem cell23_7630864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_7630864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630864 prefixEnd_7630864 := by exact prefixLift 7630864
  have htrace : WordTrace (prefixWord ++ tailWord_7630864) baseStart_7630864 baseEnd_7630864 := by
    simpa [prefixWord, tailWord_7630864, baseEnd_7630864] using wordTrace_append hprefix tailTrace_7630864
  have hstable : (prefixWord ++ tailWord_7630864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630864).length < 2 ^ (prefixWord ++ tailWord_7630864).sum := by decide
  have hdescent : baseEnd_7630864 < baseStart_7630864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7630901 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_7630901 : Nat := 118140960795 + 7630901 * 2 ^ 59
def prefixEnd_7630901 : Nat := 4983230072969 + 3 ^ 40 * 7630901 * 2
def baseEnd_7630901 : Nat := 3918320039874953798443631

theorem tailTrace_7630901 : CollatzResearch.WordTrace tailWord_7630901 prefixEnd_7630901 3918320039874953798443631 := by
  unfold tailWord_7630901
  simp only [CollatzResearch.WordTrace]
  refine ⟨278321824527556405978548557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185547883018370937319032371 278321824527556405978548557)
  ·
    refine ⟨104370684197833652241955709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278321824527556405978548557 104370684197833652241955709)
    ·
      refine ⟨39139006574187619590733391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104370684197833652241955709 39139006574187619590733391)
      ·
        refine ⟨58708509861281429386100087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39139006574187619590733391 58708509861281429386100087)
        ·
          refine ⟨88062764791922144079150131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58708509861281429386100087 88062764791922144079150131)
          ·
            refine ⟨132094147187883216118725197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88062764791922144079150131 132094147187883216118725197)
            ·
              refine ⟨49535305195456206044521949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132094147187883216118725197 49535305195456206044521949)
              ·
                refine ⟨18575739448296077266695731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49535305195456206044521949 18575739448296077266695731)
                ·
                  refine ⟨27863609172444115900043597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18575739448296077266695731 27863609172444115900043597)
                  ·
                    refine ⟨10448853439666543462516349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27863609172444115900043597 10448853439666543462516349)
                    ·
                      refine ⟨3918320039874953798443631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10448853439666543462516349 3918320039874953798443631)
                      ·
                        rfl

theorem cell23_7630901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_7630901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7630901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7630901 prefixEnd_7630901 := by exact prefixLift 7630901
  have htrace : WordTrace (prefixWord ++ tailWord_7630901) baseStart_7630901 baseEnd_7630901 := by
    simpa [prefixWord, tailWord_7630901, baseEnd_7630901] using wordTrace_append hprefix tailTrace_7630901
  have hstable : (prefixWord ++ tailWord_7630901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7630901).length < 2 ^ (prefixWord ++ tailWord_7630901).sum := by decide
  have hdescent : baseEnd_7630901 < baseStart_7630901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7630901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631009 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7631009 : Nat := 118140960795 + 7631009 * 2 ^ 59
def prefixEnd_7631009 : Nat := 4983230072969 + 3 ^ 40 * 7631009 * 2
def baseEnd_7631009 : Nat := 3918375495785639375893135

theorem tailTrace_7631009 : CollatzResearch.WordTrace tailWord_7631009 prefixEnd_7631009 3918375495785639375893135 := by
  unfold tailWord_7631009
  simp only [CollatzResearch.WordTrace]
  refine ⟨278325763611165140423480081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185550509074110093615653387 278325763611165140423480081)
  ·
    refine ⟨208744322708373855317610061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278325763611165140423480081 208744322708373855317610061)
    ·
      refine ⟨78279121015640195744103773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208744322708373855317610061 78279121015640195744103773)
      ·
        refine ⟨29354670380865073404038915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78279121015640195744103773 29354670380865073404038915)
        ·
          refine ⟨44032005571297610106058373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29354670380865073404038915 44032005571297610106058373)
          ·
            refine ⟨8256001044618301894885945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44032005571297610106058373 8256001044618301894885945)
            ·
              refine ⟨6192000783463726421164459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8256001044618301894885945 6192000783463726421164459)
              ·
                refine ⟨9288001175195589631746689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192000783463726421164459 9288001175195589631746689)
                ·
                  refine ⟨6966000881396692223810017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9288001175195589631746689 6966000881396692223810017)
                  ·
                    refine ⟨5224500661047519167857513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6966000881396692223810017 5224500661047519167857513)
                    ·
                      refine ⟨3918375495785639375893135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224500661047519167857513 3918375495785639375893135)
                      ·
                        rfl

theorem cell23_7631009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7631009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631009 prefixEnd_7631009 := by exact prefixLift 7631009
  have htrace : WordTrace (prefixWord ++ tailWord_7631009) baseStart_7631009 baseEnd_7631009 := by
    simpa [prefixWord, tailWord_7631009, baseEnd_7631009] using wordTrace_append hprefix tailTrace_7631009
  have hstable : (prefixWord ++ tailWord_7631009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631009).length < 2 ^ (prefixWord ++ tailWord_7631009).sum := by decide
  have hdescent : baseEnd_7631009 < baseStart_7631009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631048 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_7631048 : Nat := 118140960795 + 7631048 * 2 ^ 59
def prefixEnd_7631048 : Nat := 4983230072969 + 3 ^ 40 * 7631048 * 2
def baseEnd_7631048 : Nat := 3918395521531164723305455

theorem tailTrace_7631048 : CollatzResearch.WordTrace tailWord_7631048 prefixEnd_7631048 3918395521531164723305455 := by
  unfold tailWord_7631048
  simp only [CollatzResearch.WordTrace]
  refine ⟨139163593029011925042074899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185551457372015900056099865 139163593029011925042074899)
  ·
    refine ⟨208745389543517887563112349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139163593029011925042074899 208745389543517887563112349)
    ·
      refine ⟨78279521078819207836167131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208745389543517887563112349 78279521078819207836167131)
      ·
        refine ⟨117419281618228811754250697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78279521078819207836167131 117419281618228811754250697)
        ·
          refine ⟨88064461213671608815688023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117419281618228811754250697 88064461213671608815688023)
          ·
            refine ⟨132096691820507413223532035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88064461213671608815688023 132096691820507413223532035)
            ·
              refine ⟨198145037730761119835298053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132096691820507413223532035 198145037730761119835298053)
              ·
                refine ⟨37152194574517709969118385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198145037730761119835298053 37152194574517709969118385)
                ·
                  refine ⟨27864145930888282476838789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37152194574517709969118385 27864145930888282476838789)
                  ·
                    refine ⟨5224527362041552964407273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27864145930888282476838789 5224527362041552964407273)
                    ·
                      refine ⟨3918395521531164723305455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224527362041552964407273 3918395521531164723305455)
                      ·
                        rfl

theorem cell23_7631048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_7631048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631048 prefixEnd_7631048 := by exact prefixLift 7631048
  have htrace : WordTrace (prefixWord ++ tailWord_7631048) baseStart_7631048 baseEnd_7631048 := by
    simpa [prefixWord, tailWord_7631048, baseEnd_7631048] using wordTrace_append hprefix tailTrace_7631048
  have hstable : (prefixWord ++ tailWord_7631048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631048).length < 2 ^ (prefixWord ++ tailWord_7631048).sum := by decide
  have hdescent : baseEnd_7631048 < baseStart_7631048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631081 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_7631081 : Nat := 118140960795 + 7631081 * 2 ^ 59
def prefixEnd_7631081 : Nat := 4983230072969 + 3 ^ 40 * 7631081 * 2
def baseEnd_7631081 : Nat := 3918412466392763094192803

theorem tailTrace_7631081 : CollatzResearch.WordTrace tailWord_7631081 prefixEnd_7631081 3918412466392763094192803 := by
  unfold tailWord_7631081
  simp only [CollatzResearch.WordTrace]
  refine ⟨278328389666904296720101097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185552259777936197813400731 278328389666904296720101097)
  ·
    refine ⟨208746292250178222540075823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278328389666904296720101097 208746292250178222540075823)
    ·
      refine ⟨313119438375267333810113735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208746292250178222540075823 313119438375267333810113735)
      ·
        refine ⟨469679157562901000715170603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313119438375267333810113735 469679157562901000715170603)
        ·
          refine ⟨704518736344351501072755905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469679157562901000715170603 704518736344351501072755905)
          ·
            refine ⟨528389052258263625804566929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704518736344351501072755905 528389052258263625804566929)
            ·
              refine ⟨396291789193697719353425197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528389052258263625804566929 396291789193697719353425197)
              ·
                refine ⟨148609420947636644757534449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396291789193697719353425197 148609420947636644757534449)
                ·
                  refine ⟨111457065710727483568150837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148609420947636644757534449 111457065710727483568150837)
                  ·
                    refine ⟨10449099910380701584514141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111457065710727483568150837 10449099910380701584514141)
                    ·
                      refine ⟨3918412466392763094192803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449099910380701584514141 3918412466392763094192803)
                      ·
                        rfl

theorem cell23_7631081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_7631081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631081 prefixEnd_7631081 := by exact prefixLift 7631081
  have htrace : WordTrace (prefixWord ++ tailWord_7631081) baseStart_7631081 baseEnd_7631081 := by
    simpa [prefixWord, tailWord_7631081, baseEnd_7631081] using wordTrace_append hprefix tailTrace_7631081
  have hstable : (prefixWord ++ tailWord_7631081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631081).length < 2 ^ (prefixWord ++ tailWord_7631081).sum := by decide
  have hdescent : baseEnd_7631081 < baseStart_7631081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631085 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_7631085 : Nat := 118140960795 + 7631085 * 2 ^ 59
def prefixEnd_7631085 : Nat := 4983230072969 + 3 ^ 40 * 7631085 * 2
def baseEnd_7631085 : Nat := 3918414520315381078542785

theorem tailTrace_7631085 : CollatzResearch.WordTrace tailWord_7631085 prefixEnd_7631085 3918414520315381078542785 := by
  unfold tailWord_7631085
  simp only [CollatzResearch.WordTrace]
  refine ⟨278328535558889805403246709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185552357039259870268831139 278328535558889805403246709)
  ·
    refine ⟨26093300208645919256554379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278328535558889805403246709 26093300208645919256554379)
    ·
      refine ⟨39139950312968878884831569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26093300208645919256554379 39139950312968878884831569)
      ·
        refine ⟨29354962734726659163623677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39139950312968878884831569 29354962734726659163623677)
        ·
          refine ⟨11008111025522497186358879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29354962734726659163623677 11008111025522497186358879)
          ·
            refine ⟨16512166538283745779538319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008111025522497186358879 16512166538283745779538319)
            ·
              refine ⟨24768249807425618669307479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512166538283745779538319 24768249807425618669307479)
              ·
                refine ⟨37152374711138428003961219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24768249807425618669307479 37152374711138428003961219)
                ·
                  refine ⟨55728562066707642005941829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37152374711138428003961219 55728562066707642005941829)
                  ·
                    refine ⟨10449105387507682876114093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55728562066707642005941829 10449105387507682876114093)
                    ·
                      refine ⟨3918414520315381078542785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449105387507682876114093 3918414520315381078542785)
                      ·
                        rfl

theorem cell23_7631085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_7631085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631085 prefixEnd_7631085 := by exact prefixLift 7631085
  have htrace : WordTrace (prefixWord ++ tailWord_7631085) baseStart_7631085 baseEnd_7631085 := by
    simpa [prefixWord, tailWord_7631085, baseEnd_7631085] using wordTrace_append hprefix tailTrace_7631085
  have hstable : (prefixWord ++ tailWord_7631085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631085).length < 2 ^ (prefixWord ++ tailWord_7631085).sum := by decide
  have hdescent : baseEnd_7631085 < baseStart_7631085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631115 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 3]
def baseStart_7631115 : Nat := 118140960795 + 7631115 * 2 ^ 59
def prefixEnd_7631115 : Nat := 4983230072969 + 3 ^ 40 * 7631115 * 2
def baseEnd_7631115 : Nat := 3918429924735015961167647

theorem tailTrace_7631115 : CollatzResearch.WordTrace tailWord_7631115 prefixEnd_7631115 3918429924735015961167647 := by
  unfold tailWord_7631115
  simp only [CollatzResearch.WordTrace]
  refine ⟨278329629748781120526838799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185553086499187413684559199 278329629748781120526838799)
  ·
    refine ⟨417494444623171680790258199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278329629748781120526838799 417494444623171680790258199)
    ·
      refine ⟨626241666934757521185387299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417494444623171680790258199 626241666934757521185387299)
      ·
        refine ⟨939362500402136281778080949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626241666934757521185387299 939362500402136281778080949)
        ·
          refine ⟨88065234412700276416695089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 939362500402136281778080949 88065234412700276416695089)
          ·
            refine ⟨66048925809525207312521317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88065234412700276416695089 66048925809525207312521317)
            ·
              refine ⟨12384173589285976371097747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66048925809525207312521317 12384173589285976371097747)
              ·
                refine ⟨18576260383928964556646621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12384173589285976371097747 18576260383928964556646621)
                ·
                  refine ⟨6966097643973361708742483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18576260383928964556646621 6966097643973361708742483)
                  ·
                    refine ⟨10449146465960042563113725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966097643973361708742483 10449146465960042563113725)
                    ·
                      refine ⟨3918429924735015961167647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449146465960042563113725 3918429924735015961167647)
                      ·
                        rfl

theorem cell23_7631115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 1, 3].length) (baseStart_7631115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631115 prefixEnd_7631115 := by exact prefixLift 7631115
  have htrace : WordTrace (prefixWord ++ tailWord_7631115) baseStart_7631115 baseEnd_7631115 := by
    simpa [prefixWord, tailWord_7631115, baseEnd_7631115] using wordTrace_append hprefix tailTrace_7631115
  have hstable : (prefixWord ++ tailWord_7631115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631115).length < 2 ^ (prefixWord ++ tailWord_7631115).sum := by decide
  have hdescent : baseEnd_7631115 < baseStart_7631115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631135 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 1, 5]
def baseStart_7631135 : Nat := 118140960795 + 7631135 * 2 ^ 59
def prefixEnd_7631135 : Nat := 4983230072969 + 3 ^ 40 * 7631135 * 2
def baseEnd_7631135 : Nat := 1306146731449368627639185

theorem tailTrace_7631135 : CollatzResearch.WordTrace tailWord_7631135 prefixEnd_7631135 1306146731449368627639185 := by
  unfold tailWord_7631135
  simp only [CollatzResearch.WordTrace]
  refine ⟨278330359208708663942566859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185553572805805775961711239 278330359208708663942566859)
  ·
    refine ⟨417495538813062995913850289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278330359208708663942566859 417495538813062995913850289)
    ·
      refine ⟨313121654109797246935387717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417495538813062995913850289 313121654109797246935387717)
      ·
        refine ⟨58710310145586983800385197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313121654109797246935387717 58710310145586983800385197)
        ·
          refine ⟨22016366304595118925144449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58710310145586983800385197 22016366304595118925144449)
          ·
            refine ⟨16512274728446339193858337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22016366304595118925144449 16512274728446339193858337)
            ·
              refine ⟨12384206046334754395393753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16512274728446339193858337 12384206046334754395393753)
              ·
                refine ⟨9288154534751065796545315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12384206046334754395393753 9288154534751065796545315)
                ·
                  refine ⟨13932231802126598694817973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288154534751065796545315 13932231802126598694817973)
                  ·
                    refine ⟨1306146731449368627639185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13932231802126598694817973 1306146731449368627639185)
                    ·
                      rfl

theorem cell23_7631135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_7631135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631135 prefixEnd_7631135 := by exact prefixLift 7631135
  have htrace : WordTrace (prefixWord ++ tailWord_7631135) baseStart_7631135 baseEnd_7631135 := by
    simpa [prefixWord, tailWord_7631135, baseEnd_7631135] using wordTrace_append hprefix tailTrace_7631135
  have hstable : (prefixWord ++ tailWord_7631135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631135).length < 2 ^ (prefixWord ++ tailWord_7631135).sum := by decide
  have hdescent : baseEnd_7631135 < baseStart_7631135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631143 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7631143 : Nat := 118140960795 + 7631143 * 2 ^ 59
def prefixEnd_7631143 : Nat := 4983230072969 + 3 ^ 40 * 7631143 * 2
def baseEnd_7631143 : Nat := 1306148100731113950539173

theorem tailTrace_7631143 : CollatzResearch.WordTrace tailWord_7631143 prefixEnd_7631143 1306148100731113950539173 := by
  unfold tailWord_7631143
  simp only [CollatzResearch.WordTrace]
  refine ⟨278330650992679681308858083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185553767328453120872572055 278330650992679681308858083)
  ·
    refine ⟨417495976489019521963287125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278330650992679681308858083 417495976489019521963287125)
    ·
      refine ⟨4892530974480697523007271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 417495976489019521963287125 4892530974480697523007271)
      ·
        refine ⟨7338796461721046284510907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892530974480697523007271 7338796461721046284510907)
        ·
          refine ⟨11008194692581569426766361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338796461721046284510907 11008194692581569426766361)
          ·
            refine ⟨8256146019436177070074771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11008194692581569426766361 8256146019436177070074771)
            ·
              refine ⟨12384219029154265605112157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256146019436177070074771 12384219029154265605112157)
              ·
                refine ⟨4644082135932849601917059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12384219029154265605112157 4644082135932849601917059)
                ·
                  refine ⟨6966123203899274402875589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644082135932849601917059 6966123203899274402875589)
                  ·
                    refine ⟨1306148100731113950539173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966123203899274402875589 1306148100731113950539173)
                    ·
                      rfl

theorem cell23_7631143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7631143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631143 prefixEnd_7631143 := by exact prefixLift 7631143
  have htrace : WordTrace (prefixWord ++ tailWord_7631143) baseStart_7631143 baseEnd_7631143 := by
    simpa [prefixWord, tailWord_7631143, baseEnd_7631143] using wordTrace_append hprefix tailTrace_7631143
  have hstable : (prefixWord ++ tailWord_7631143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631143).length < 2 ^ (prefixWord ++ tailWord_7631143).sum := by decide
  have hdescent : baseEnd_7631143 < baseStart_7631143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631148 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_7631148 : Nat := 118140960795 + 7631148 * 2 ^ 59
def prefixEnd_7631148 : Nat := 4983230072969 + 3 ^ 40 * 7631148 * 2
def baseEnd_7631148 : Nat := 1306148956532204777351665

theorem tailTrace_7631148 : CollatzResearch.WordTrace tailWord_7631148 prefixEnd_7631148 1306148956532204777351665 := by
  unfold tailWord_7631148
  simp only [CollatzResearch.WordTrace]
  refine ⟨139165416678830783581395049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185553888905107711441860065 139165416678830783581395049)
  ·
    refine ⟨104374062509123087686046287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139165416678830783581395049 104374062509123087686046287)
    ·
      refine ⟨156561093763684631529069431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104374062509123087686046287 156561093763684631529069431)
      ·
        refine ⟨234841640645526947293604147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156561093763684631529069431 234841640645526947293604147)
        ·
          refine ⟨352262460968290420940406221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234841640645526947293604147 352262460968290420940406221)
          ·
            refine ⟨132098422863108907852652333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352262460968290420940406221 132098422863108907852652333)
            ·
              refine ⟨49536908573665840444744625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132098422863108907852652333 49536908573665840444744625)
              ·
                refine ⟨37152681430249380333558469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49536908573665840444744625 37152681430249380333558469)
                ·
                  refine ⟨6966127768171758812542213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37152681430249380333558469 6966127768171758812542213)
                  ·
                    refine ⟨1306148956532204777351665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966127768171758812542213 1306148956532204777351665)
                    ·
                      rfl

theorem cell23_7631148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_7631148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631148 prefixEnd_7631148 := by exact prefixLift 7631148
  have htrace : WordTrace (prefixWord ++ tailWord_7631148) baseStart_7631148 baseEnd_7631148 := by
    simpa [prefixWord, tailWord_7631148, baseEnd_7631148] using wordTrace_append hprefix tailTrace_7631148
  have hstable : (prefixWord ++ tailWord_7631148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631148).length < 2 ^ (prefixWord ++ tailWord_7631148).sum := by decide
  have hdescent : baseEnd_7631148 < baseStart_7631148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631166 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_7631166 : Nat := 118140960795 + 7631166 * 2 ^ 59
def prefixEnd_7631166 : Nat := 4983230072969 + 3 ^ 40 * 7631166 * 2
def baseEnd_7631166 : Nat := 3918456112248395261629913

theorem tailTrace_7631166 : CollatzResearch.WordTrace tailWord_7631166 prefixEnd_7631166 3918456112248395261629913 := by
  unfold tailWord_7631166
  simp only [CollatzResearch.WordTrace]
  refine ⟨34791436233949544529618169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185554326581064237491296901 34791436233949544529618169)
  ·
    refine ⟨26093577175462158397213627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34791436233949544529618169 26093577175462158397213627)
    ·
      refine ⟨39140365763193237595820441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26093577175462158397213627 39140365763193237595820441)
      ·
        refine ⟨29355274322394928196865331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39140365763193237595820441 29355274322394928196865331)
        ·
          refine ⟨44032911483592392295297997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29355274322394928196865331 44032911483592392295297997)
          ·
            refine ⟨16512341806347147110736749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44032911483592392295297997 16512341806347147110736749)
            ·
              refine ⟨6192128177380180166526281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16512341806347147110736749 6192128177380180166526281)
              ·
                refine ⟨4644096133035135124894711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192128177380180166526281 4644096133035135124894711)
                ·
                  refine ⟨6966144199552702687342067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644096133035135124894711 6966144199552702687342067)
                  ·
                    refine ⟨10449216299329054031013101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966144199552702687342067 10449216299329054031013101)
                    ·
                      refine ⟨3918456112248395261629913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449216299329054031013101 3918456112248395261629913)
                      ·
                        rfl

theorem cell23_7631166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_7631166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631166 prefixEnd_7631166 := by exact prefixLift 7631166
  have htrace : WordTrace (prefixWord ++ tailWord_7631166) baseStart_7631166 baseEnd_7631166 := by
    simpa [prefixWord, tailWord_7631166, baseEnd_7631166] using wordTrace_append hprefix tailTrace_7631166
  have hstable : (prefixWord ++ tailWord_7631166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631166).length < 2 ^ (prefixWord ++ tailWord_7631166).sum := by decide
  have hdescent : baseEnd_7631166 < baseStart_7631166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631189 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_7631189 : Nat := 118140960795 + 7631189 * 2 ^ 59
def prefixEnd_7631189 : Nat := 4983230072969 + 3 ^ 40 * 7631189 * 2
def baseEnd_7631189 : Nat := 3918467922303448671642307

theorem tailTrace_7631189 : CollatzResearch.WordTrace tailWord_7631189 prefixEnd_7631189 3918467922303448671642307 := by
  unfold tailWord_7631189
  simp only [CollatzResearch.WordTrace]
  refine ⟨278332328750513031165032621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185554885833675354110021747 278332328750513031165032621)
  ·
    refine ⟨104374623281442386686887233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278332328750513031165032621 104374623281442386686887233)
    ·
      refine ⟨78280967461081790015165425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104374623281442386686887233 78280967461081790015165425)
      ·
        refine ⟨58710725595811342511374069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78280967461081790015165425 58710725595811342511374069)
        ·
          refine ⟨5504130524607313360441319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58710725595811342511374069 5504130524607313360441319)
          ·
            refine ⟨8256195786910970040661979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504130524607313360441319 8256195786910970040661979)
            ·
              refine ⟨12384293680366455060992969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256195786910970040661979 12384293680366455060992969)
              ·
                refine ⟨9288220260274841295744727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12384293680366455060992969 9288220260274841295744727)
                ·
                  refine ⟨13932330390412261943617091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288220260274841295744727 13932330390412261943617091)
                  ·
                    refine ⟨20898495585618392915425637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13932330390412261943617091 20898495585618392915425637)
                    ·
                      refine ⟨3918467922303448671642307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20898495585618392915425637 3918467922303448671642307)
                      ·
                        rfl

theorem cell23_7631189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_7631189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631189 prefixEnd_7631189 := by exact prefixLift 7631189
  have htrace : WordTrace (prefixWord ++ tailWord_7631189) baseStart_7631189 baseEnd_7631189 := by
    simpa [prefixWord, tailWord_7631189, baseEnd_7631189] using wordTrace_append hprefix tailTrace_7631189
  have hstable : (prefixWord ++ tailWord_7631189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631189).length < 2 ^ (prefixWord ++ tailWord_7631189).sum := by decide
  have hdescent : baseEnd_7631189 < baseStart_7631189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631205 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_7631205 : Nat := 118140960795 + 7631205 * 2 ^ 59
def prefixEnd_7631205 : Nat := 4983230072969 + 3 ^ 40 * 7631205 * 2
def baseEnd_7631205 : Nat := 3918476137993920609042233

theorem tailTrace_7631205 : CollatzResearch.WordTrace tailWord_7631205 prefixEnd_7631205 3918476137993920609042233 := by
  unfold tailWord_7631205
  simp only [CollatzResearch.WordTrace]
  refine ⟨278332912318455065897615069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185555274878970043931743379 278332912318455065897615069)
  ·
    refine ⟨104374842119420649711605651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278332912318455065897615069 104374842119420649711605651)
    ·
      refine ⟨156562263179130974567408477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104374842119420649711605651 156562263179130974567408477)
      ·
        refine ⟨58710848692174115462778179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156562263179130974567408477 58710848692174115462778179)
        ·
          refine ⟨88066273038261173194167269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58710848692174115462778179 88066273038261173194167269)
          ·
            refine ⟨16512426194673969973906363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88066273038261173194167269 16512426194673969973906363)
            ·
              refine ⟨24768639292010954960859545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512426194673969973906363 24768639292010954960859545)
              ·
                refine ⟨18576479469008216220644659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24768639292010954960859545 18576479469008216220644659)
                ·
                  refine ⟨27864719203512324330966989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18576479469008216220644659 27864719203512324330966989)
                  ·
                    refine ⟨10449269701317121624112621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27864719203512324330966989 10449269701317121624112621)
                    ·
                      refine ⟨3918476137993920609042233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449269701317121624112621 3918476137993920609042233)
                      ·
                        rfl

theorem cell23_7631205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_7631205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631205 prefixEnd_7631205 := by exact prefixLift 7631205
  have htrace : WordTrace (prefixWord ++ tailWord_7631205) baseStart_7631205 baseEnd_7631205 := by
    simpa [prefixWord, tailWord_7631205, baseEnd_7631205] using wordTrace_append hprefix tailTrace_7631205
  have hstable : (prefixWord ++ tailWord_7631205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631205).length < 2 ^ (prefixWord ++ tailWord_7631205).sum := by decide
  have hdescent : baseEnd_7631205 < baseStart_7631205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631211 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_7631211 : Nat := 118140960795 + 7631211 * 2 ^ 59
def prefixEnd_7631211 : Nat := 4983230072969 + 3 ^ 40 * 7631211 * 2
def baseEnd_7631211 : Nat := 3918479218877847585567205

theorem tailTrace_7631211 : CollatzResearch.WordTrace tailWord_7631211 prefixEnd_7631211 3918479218877847585567205 := by
  unfold tailWord_7631211
  simp only [CollatzResearch.WordTrace]
  refine ⟨278333131156433328922333487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185555420770955552614888991 278333131156433328922333487)
  ·
    refine ⟨417499696734649993383500231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278333131156433328922333487 417499696734649993383500231)
    ·
      refine ⟨626249545101974990075250347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417499696734649993383500231 626249545101974990075250347)
      ·
        refine ⟨939374317652962485112875521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626249545101974990075250347 939374317652962485112875521)
        ·
          refine ⟨704530738239721863834656641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 939374317652962485112875521 704530738239721863834656641)
          ·
            refine ⟨528398053679791397875992481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704530738239721863834656641 528398053679791397875992481)
            ·
              refine ⟨396298540259843548406994361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528398053679791397875992481 396298540259843548406994361)
              ·
                refine ⟨297223905194882661305245771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396298540259843548406994361 297223905194882661305245771)
                ·
                  refine ⟨445835857792323991957868657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297223905194882661305245771 445835857792323991957868657)
                  ·
                    refine ⟨334376893344242993968401493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 445835857792323991957868657 334376893344242993968401493)
                    ·
                      refine ⟨3918479218877847585567205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334376893344242993968401493 3918479218877847585567205)
                      ·
                        rfl

theorem cell23_7631211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_7631211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631211 prefixEnd_7631211 := by exact prefixLift 7631211
  have htrace : WordTrace (prefixWord ++ tailWord_7631211) baseStart_7631211 baseEnd_7631211 := by
    simpa [prefixWord, tailWord_7631211, baseEnd_7631211] using wordTrace_append hprefix tailTrace_7631211
  have hstable : (prefixWord ++ tailWord_7631211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631211).length < 2 ^ (prefixWord ++ tailWord_7631211).sum := by decide
  have hdescent : baseEnd_7631211 < baseStart_7631211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631305 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 5, 2]
def baseStart_7631305 : Nat := 118140960795 + 7631305 * 2 ^ 59
def prefixEnd_7631305 : Nat := 4983230072969 + 3 ^ 40 * 7631305 * 2
def baseEnd_7631305 : Nat := 3918527486059370217791773

theorem tailTrace_7631305 : CollatzResearch.WordTrace tailWord_7631305 prefixEnd_7631305 3918527486059370217791773 := by
  unfold tailWord_7631305
  simp only [CollatzResearch.WordTrace]
  refine ⟨278336559618092782976255369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185557706412061855317503579 278336559618092782976255369)
  ·
    refine ⟨208752419713569587232191527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278336559618092782976255369 208752419713569587232191527)
    ·
      refine ⟨313128629570354380848287291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208752419713569587232191527 313128629570354380848287291)
      ·
        refine ⟨469692944355531571272430937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313128629570354380848287291 469692944355531571272430937)
        ·
          refine ⟨352269708266648678454323203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469692944355531571272430937 352269708266648678454323203)
          ·
            refine ⟨528404562399973017681484805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352269708266648678454323203 528404562399973017681484805)
            ·
              refine ⟨99075855449994940815278401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528404562399973017681484805 99075855449994940815278401)
              ·
                refine ⟨74306891587496205611458801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99075855449994940815278401 74306891587496205611458801)
                ·
                  refine ⟨55730168690622154208594101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74306891587496205611458801 55730168690622154208594101)
                  ·
                    refine ⟨5224703314745826957055697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55730168690622154208594101 5224703314745826957055697)
                    ·
                      refine ⟨3918527486059370217791773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224703314745826957055697 3918527486059370217791773)
                      ·
                        rfl

theorem cell23_7631305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5, 2].length) (baseStart_7631305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631305 prefixEnd_7631305 := by exact prefixLift 7631305
  have htrace : WordTrace (prefixWord ++ tailWord_7631305) baseStart_7631305 baseEnd_7631305 := by
    simpa [prefixWord, tailWord_7631305, baseEnd_7631305] using wordTrace_append hprefix tailTrace_7631305
  have hstable : (prefixWord ++ tailWord_7631305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631305).length < 2 ^ (prefixWord ++ tailWord_7631305).sum := by decide
  have hdescent : baseEnd_7631305 < baseStart_7631305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631325 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7631325 : Nat := 118140960795 + 7631325 * 2 ^ 59
def prefixEnd_7631325 : Nat := 4983230072969 + 3 ^ 40 * 7631325 * 2
def baseEnd_7631325 : Nat := 3918537755672460139541681

theorem tailTrace_7631325 : CollatzResearch.WordTrace tailWord_7631325 prefixEnd_7631325 3918537755672460139541681 := by
  unfold tailWord_7631325
  simp only [CollatzResearch.WordTrace]
  refine ⟨278337289078020326391983429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185558192718680217594655619 278337289078020326391983429)
  ·
    refine ⟨52188241702128811198496893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278337289078020326391983429 52188241702128811198496893)
    ·
      refine ⟨19570590638298304199436335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52188241702128811198496893 19570590638298304199436335)
      ·
        refine ⟨29355885957447456299154503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19570590638298304199436335 29355885957447456299154503)
        ·
          refine ⟨44033828936171184448731755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29355885957447456299154503 44033828936171184448731755)
          ·
            refine ⟨66050743404256776673097633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44033828936171184448731755 66050743404256776673097633)
            ·
              refine ⟨49538057553192582504823225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66050743404256776673097633 49538057553192582504823225)
              ·
                refine ⟨37153543164894436878617419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49538057553192582504823225 37153543164894436878617419)
                ·
                  refine ⟨55730314747341655317926129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37153543164894436878617419 55730314747341655317926129)
                  ·
                    refine ⟨41797736060506241488444597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55730314747341655317926129 41797736060506241488444597)
                    ·
                      refine ⟨3918537755672460139541681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41797736060506241488444597 3918537755672460139541681)
                      ·
                        rfl

theorem cell23_7631325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7631325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631325 prefixEnd_7631325 := by exact prefixLift 7631325
  have htrace : WordTrace (prefixWord ++ tailWord_7631325) baseStart_7631325 baseEnd_7631325 := by
    simpa [prefixWord, tailWord_7631325, baseEnd_7631325] using wordTrace_append hprefix tailTrace_7631325
  have hstable : (prefixWord ++ tailWord_7631325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631325).length < 2 ^ (prefixWord ++ tailWord_7631325).sum := by decide
  have hdescent : baseEnd_7631325 < baseStart_7631325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631366 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7631366 : Nat := 118140960795 + 7631366 * 2 ^ 59
def prefixEnd_7631366 : Nat := 4983230072969 + 3 ^ 40 * 7631366 * 2
def baseEnd_7631366 : Nat := 1306186269459764826376331

theorem tailTrace_7631366 : CollatzResearch.WordTrace tailWord_7631366 prefixEnd_7631366 1306186269459764826376331 := by
  unfold tailWord_7631366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8698087014714743449819561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185559189647247860262817301 8698087014714743449819561)
  ·
    refine ⟨6523565261036057587364671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8698087014714743449819561 6523565261036057587364671)
    ·
      refine ⟨9785347891554086381047007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6523565261036057587364671 9785347891554086381047007)
      ·
        refine ⟨14678021837331129571570511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785347891554086381047007 14678021837331129571570511)
        ·
          refine ⟨22017032755996694357355767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14678021837331129571570511 22017032755996694357355767)
          ·
            refine ⟨33025549133995041536033651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22017032755996694357355767 33025549133995041536033651)
            ·
              refine ⟨49538323700992562304050477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33025549133995041536033651 49538323700992562304050477)
              ·
                refine ⟨18576871387872210864018929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49538323700992562304050477 18576871387872210864018929)
                ·
                  refine ⟨13932653540904158148014197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18576871387872210864018929 13932653540904158148014197)
                  ·
                    refine ⟨1306186269459764826376331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13932653540904158148014197 1306186269459764826376331)
                    ·
                      rfl

theorem cell23_7631366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7631366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631366 prefixEnd_7631366 := by exact prefixLift 7631366
  have htrace : WordTrace (prefixWord ++ tailWord_7631366) baseStart_7631366 baseEnd_7631366 := by
    simpa [prefixWord, tailWord_7631366, baseEnd_7631366] using wordTrace_append hprefix tailTrace_7631366
  have hstable : (prefixWord ++ tailWord_7631366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631366).length < 2 ^ (prefixWord ++ tailWord_7631366).sum := by decide
  have hdescent : baseEnd_7631366 < baseStart_7631366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631372 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_7631372 : Nat := 118140960795 + 7631372 * 2 ^ 59
def prefixEnd_7631372 : Nat := 4983230072969 + 3 ^ 40 * 7631372 * 2
def baseEnd_7631372 : Nat := 3918561889263221455653965

theorem tailTrace_7631372 : CollatzResearch.WordTrace tailWord_7631372 prefixEnd_7631372 3918561889263221455653965 := by
  unfold tailWord_7631372
  simp only [CollatzResearch.WordTrace]
  refine ⟨139169501654425026709472185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185559335539233368945962913 139169501654425026709472185)
  ·
    refine ⟨104377126240818770032104139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139169501654425026709472185 104377126240818770032104139)
    ·
      refine ⟨156565689361228155048156209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104377126240818770032104139 156565689361228155048156209)
      ·
        refine ⟨117424267020921116286117157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156565689361228155048156209 117424267020921116286117157)
        ·
          refine ⟨22017050066422709303646967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117424267020921116286117157 22017050066422709303646967)
          ·
            refine ⟨33025575099634063955470451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22017050066422709303646967 33025575099634063955470451)
            ·
              refine ⟨49538362649451095933205677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33025575099634063955470451 49538362649451095933205677)
              ·
                refine ⟨18576885993544160974952129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49538362649451095933205677 18576885993544160974952129)
                ·
                  refine ⟨13932664495158120731214097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18576885993544160974952129 13932664495158120731214097)
                  ·
                    refine ⟨10449498371368590548410573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13932664495158120731214097 10449498371368590548410573)
                    ·
                      refine ⟨3918561889263221455653965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449498371368590548410573 3918561889263221455653965)
                      ·
                        rfl

theorem cell23_7631372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_7631372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631372 prefixEnd_7631372 := by exact prefixLift 7631372
  have htrace : WordTrace (prefixWord ++ tailWord_7631372) baseStart_7631372 baseEnd_7631372 := by
    simpa [prefixWord, tailWord_7631372, baseEnd_7631372] using wordTrace_append hprefix tailTrace_7631372
  have hstable : (prefixWord ++ tailWord_7631372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631372).length < 2 ^ (prefixWord ++ tailWord_7631372).sum := by decide
  have hdescent : baseEnd_7631372 < baseStart_7631372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631429 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_7631429 : Nat := 118140960795 + 7631429 * 2 ^ 59
def prefixEnd_7631429 : Nat := 4983230072969 + 3 ^ 40 * 7631429 * 2
def baseEnd_7631429 : Nat := 3918591157660527732641203

theorem tailTrace_7631429 : CollatzResearch.WordTrace tailWord_7631429 prefixEnd_7631429 3918591157660527732641203 := by
  unfold tailWord_7631429
  simp only [CollatzResearch.WordTrace]
  refine ⟨278341082269643552153769341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185560721513095701435846227 278341082269643552153769341)
  ·
    refine ⟨104377905851116332057663503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278341082269643552153769341 104377905851116332057663503)
    ·
      refine ⟨156566858776674498086495255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104377905851116332057663503 156566858776674498086495255)
      ·
        refine ⟨234850288165011747129742883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156566858776674498086495255 234850288165011747129742883)
        ·
          refine ⟨352275432247517620694614325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234850288165011747129742883 352275432247517620694614325)
          ·
            refine ⟨33025821773204776940120093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352275432247517620694614325 33025821773204776940120093)
            ·
              refine ⟨12384683164951791352545035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33025821773204776940120093 12384683164951791352545035)
              ·
                refine ⟨18577024747427687028817553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12384683164951791352545035 18577024747427687028817553)
                ·
                  refine ⟨13932768560570765271613165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18577024747427687028817553 13932768560570765271613165)
                  ·
                    refine ⟨5224788210214036976854937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13932768560570765271613165 5224788210214036976854937)
                    ·
                      refine ⟨3918591157660527732641203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224788210214036976854937 3918591157660527732641203)
                      ·
                        rfl

theorem cell23_7631429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_7631429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631429 prefixEnd_7631429 := by exact prefixLift 7631429
  have htrace : WordTrace (prefixWord ++ tailWord_7631429) baseStart_7631429 baseEnd_7631429 := by
    simpa [prefixWord, tailWord_7631429, baseEnd_7631429] using wordTrace_append hprefix tailTrace_7631429
  have hstable : (prefixWord ++ tailWord_7631429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631429).length < 2 ^ (prefixWord ++ tailWord_7631429).sum := by decide
  have hdescent : baseEnd_7631429 < baseStart_7631429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631435 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 1, 6]
def baseStart_7631435 : Nat := 118140960795 + 7631435 * 2 ^ 59
def prefixEnd_7631435 : Nat := 4983230072969 + 3 ^ 40 * 7631435 * 2
def baseEnd_7631435 : Nat := 1306198079514818236388725

theorem tailTrace_7631435 : CollatzResearch.WordTrace tailWord_7631435 prefixEnd_7631435 1306198079514818236388725 := by
  unfold tailWord_7631435
  simp only [CollatzResearch.WordTrace]
  refine ⟨278341301107621815178487759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185560867405081210118991839 278341301107621815178487759)
  ·
    refine ⟨417511951661432722767731639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278341301107621815178487759 417511951661432722767731639)
    ·
      refine ⟨626267927492149084151597459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417511951661432722767731639 626267927492149084151597459)
      ·
        refine ⟨939401891238223626227396189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626267927492149084151597459 939401891238223626227396189)
        ·
          refine ⟨352275709214333859835273571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939401891238223626227396189 352275709214333859835273571)
          ·
            refine ⟨528413563821500789752910357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352275709214333859835273571 528413563821500789752910357)
            ·
              refine ⟨24769385804132849519667673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 528413563821500789752910357 24769385804132849519667673)
              ·
                refine ⟨18577039353099637139750755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24769385804132849519667673 18577039353099637139750755)
                ·
                  refine ⟨27865559029649455709626133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18577039353099637139750755 27865559029649455709626133)
                  ·
                    refine ⟨1306198079514818236388725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27865559029649455709626133 1306198079514818236388725)
                    ·
                      rfl

theorem cell23_7631435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 6].length) (baseStart_7631435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631435 prefixEnd_7631435 := by exact prefixLift 7631435
  have htrace : WordTrace (prefixWord ++ tailWord_7631435) baseStart_7631435 baseEnd_7631435 := by
    simpa [prefixWord, tailWord_7631435, baseEnd_7631435] using wordTrace_append hprefix tailTrace_7631435
  have hstable : (prefixWord ++ tailWord_7631435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631435).length < 2 ^ (prefixWord ++ tailWord_7631435).sum := by decide
  have hdescent : baseEnd_7631435 < baseStart_7631435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631436 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7631436 : Nat := 118140960795 + 7631436 * 2 ^ 59
def prefixEnd_7631436 : Nat := 4983230072969 + 3 ^ 40 * 7631436 * 2
def baseEnd_7631436 : Nat := 3918594752025109205253671

theorem tailTrace_7631436 : CollatzResearch.WordTrace tailWord_7631436 prefixEnd_7631436 3918594752025109205253671 := by
  unfold tailWord_7631436
  simp only [CollatzResearch.WordTrace]
  refine ⟨139170668790309096174637081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185560891720412128232849441 139170668790309096174637081)
  ·
    refine ⟨104378001592731822130977811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139170668790309096174637081 104378001592731822130977811)
    ·
      refine ⟨156567002389097733196466717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104378001592731822130977811 156567002389097733196466717)
      ·
        refine ⟨58712625895911649948675019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156567002389097733196466717 58712625895911649948675019)
        ·
          refine ⟨88068938843867474923012529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58712625895911649948675019 88068938843867474923012529)
          ·
            refine ⟨66051704132900606192259397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88068938843867474923012529 66051704132900606192259397)
            ·
              refine ⟨12384694524918863661048637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66051704132900606192259397 12384694524918863661048637)
              ·
                refine ⟨4644260446844573872893239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12384694524918863661048637 4644260446844573872893239)
                ·
                  refine ⟨6966390670266860809339859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644260446844573872893239 6966390670266860809339859)
                  ·
                    refine ⟨10449586005400291214009789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966390670266860809339859 10449586005400291214009789)
                    ·
                      refine ⟨3918594752025109205253671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449586005400291214009789 3918594752025109205253671)
                      ·
                        rfl

theorem cell23_7631436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7631436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631436 prefixEnd_7631436 := by exact prefixLift 7631436
  have htrace : WordTrace (prefixWord ++ tailWord_7631436) baseStart_7631436 baseEnd_7631436 := by
    simpa [prefixWord, tailWord_7631436, baseEnd_7631436] using wordTrace_append hprefix tailTrace_7631436
  have hstable : (prefixWord ++ tailWord_7631436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631436).length < 2 ^ (prefixWord ++ tailWord_7631436).sum := by decide
  have hdescent : baseEnd_7631436 < baseStart_7631436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631455 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_7631455 : Nat := 118140960795 + 7631455 * 2 ^ 59
def prefixEnd_7631455 : Nat := 4983230072969 + 3 ^ 40 * 7631455 * 2
def baseEnd_7631455 : Nat := 3918604508157544630916083

theorem tailTrace_7631455 : CollatzResearch.WordTrace tailWord_7631455 prefixEnd_7631455 3918604508157544630916083 := by
  unfold tailWord_7631455
  simp only [CollatzResearch.WordTrace]
  refine ⟨278342030567549358594215819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185561353711699572396143879 278342030567549358594215819)
  ·
    refine ⟨417513045851324037891323729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278342030567549358594215819 417513045851324037891323729)
    ·
      refine ⟨313134784388493028418492797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417513045851324037891323729 313134784388493028418492797)
      ·
        refine ⟨117425544145684885656934799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313134784388493028418492797 117425544145684885656934799)
        ·
          refine ⟨176138316218527328485402199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117425544145684885656934799 176138316218527328485402199)
          ·
            refine ⟨264207474327790992728103299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176138316218527328485402199 264207474327790992728103299)
            ·
              refine ⟨396311211491686489092154949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264207474327790992728103299 396311211491686489092154949)
              ·
                refine ⟨74308352154691216704779053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396311211491686489092154949 74308352154691216704779053)
                ·
                  refine ⟨27865632058009206264292145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74308352154691216704779053 27865632058009206264292145)
                  ·
                    refine ⟨20899224043506904698219109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27865632058009206264292145 20899224043506904698219109)
                    ·
                      refine ⟨3918604508157544630916083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20899224043506904698219109 3918604508157544630916083)
                      ·
                        rfl

theorem cell23_7631455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_7631455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631455 prefixEnd_7631455 := by exact prefixLift 7631455
  have htrace : WordTrace (prefixWord ++ tailWord_7631455) baseStart_7631455 baseEnd_7631455 := by
    simpa [prefixWord, tailWord_7631455, baseEnd_7631455] using wordTrace_append hprefix tailTrace_7631455
  have hstable : (prefixWord ++ tailWord_7631455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631455).length < 2 ^ (prefixWord ++ tailWord_7631455).sum := by decide
  have hdescent : baseEnd_7631455 < baseStart_7631455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631469 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_7631469 : Nat := 118140960795 + 7631469 * 2 ^ 59
def prefixEnd_7631469 : Nat := 4983230072969 + 3 ^ 40 * 7631469 * 2
def baseEnd_7631469 : Nat := 1306203898962235858713673

theorem tailTrace_7631469 : CollatzResearch.WordTrace tailWord_7631469 prefixEnd_7631469 1306203898962235858713673 := by
  unfold tailWord_7631469
  simp only [CollatzResearch.WordTrace]
  refine ⟨278342541189498638985225461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185561694126332425990150307 278342541189498638985225461)
  ·
    refine ⟨26094613236515497404864887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278342541189498638985225461 26094613236515497404864887)
    ·
      refine ⟨39141919854773246107297331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26094613236515497404864887 39141919854773246107297331)
      ·
        refine ⟨58712879782159869160945997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39141919854773246107297331 58712879782159869160945997)
        ·
          refine ⟨22017329918309950935354749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58712879782159869160945997 22017329918309950935354749)
          ·
            refine ⟨8256498719366231600758031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22017329918309950935354749 8256498719366231600758031)
            ·
              refine ⟨12384748079049347401137047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256498719366231600758031 12384748079049347401137047)
              ·
                refine ⟨18577122118574021101705571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12384748079049347401137047 18577122118574021101705571)
                ·
                  refine ⟨27865683177861031652558357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18577122118574021101705571 27865683177861031652558357)
                  ·
                    refine ⟨1306203898962235858713673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27865683177861031652558357 1306203898962235858713673)
                    ·
                      rfl

theorem cell23_7631469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_7631469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631469 prefixEnd_7631469 := by exact prefixLift 7631469
  have htrace : WordTrace (prefixWord ++ tailWord_7631469) baseStart_7631469 baseEnd_7631469 := by
    simpa [prefixWord, tailWord_7631469, baseEnd_7631469] using wordTrace_append hprefix tailTrace_7631469
  have hstable : (prefixWord ++ tailWord_7631469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631469).length < 2 ^ (prefixWord ++ tailWord_7631469).sum := by decide
  have hdescent : baseEnd_7631469 < baseStart_7631469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631472 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_7631472 : Nat := 118140960795 + 7631472 * 2 ^ 59
def prefixEnd_7631472 : Nat := 4983230072969 + 3 ^ 40 * 7631472 * 2
def baseEnd_7631472 : Nat := 3918613237328671064403505

theorem tailTrace_7631472 : CollatzResearch.WordTrace tailWord_7631472 prefixEnd_7631472 3918613237328671064403505 := by
  unfold tailWord_7631472
  simp only [CollatzResearch.WordTrace]
  refine ⟨139171325304243885248792335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185561767072325180331723113 139171325304243885248792335)
  ·
    refine ⟨208756987956365827873188503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139171325304243885248792335 208756987956365827873188503)
    ·
      refine ⟨313135481934548741809782755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208756987956365827873188503 313135481934548741809782755)
      ·
        refine ⟨469703222901823112714674133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313135481934548741809782755 469703222901823112714674133)
        ·
          refine ⟨11008669286761479204250175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 469703222901823112714674133 11008669286761479204250175)
          ·
            refine ⟨16513003930142218806375263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008669286761479204250175 16513003930142218806375263)
            ·
              refine ⟨24769505895213328209562895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16513003930142218806375263 24769505895213328209562895)
              ·
                refine ⟨37154258842819992314344343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24769505895213328209562895 37154258842819992314344343)
                ·
                  refine ⟨55731388264229988471516515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37154258842819992314344343 55731388264229988471516515)
                  ·
                    refine ⟨83597082396344982707274773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55731388264229988471516515 83597082396344982707274773)
                    ·
                      refine ⟨3918613237328671064403505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83597082396344982707274773 3918613237328671064403505)
                      ·
                        rfl

theorem cell23_7631472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_7631472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631472 prefixEnd_7631472 := by exact prefixLift 7631472
  have htrace : WordTrace (prefixWord ++ tailWord_7631472) baseStart_7631472 baseEnd_7631472 := by
    simpa [prefixWord, tailWord_7631472, baseEnd_7631472] using wordTrace_append hprefix tailTrace_7631472
  have hstable : (prefixWord ++ tailWord_7631472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631472).length < 2 ^ (prefixWord ++ tailWord_7631472).sum := by decide
  have hdescent : baseEnd_7631472 < baseStart_7631472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631493 : List Nat := [1, 3, 1, 1, 4, 2, 3, 3, 1, 2, 2]
def baseStart_7631493 : Nat := 118140960795 + 7631493 * 2 ^ 59
def prefixEnd_7631493 : Nat := 4983230072969 + 3 ^ 40 * 7631493 * 2
def baseEnd_7631493 : Nat := 3918624020422415482240909

theorem tailTrace_7631493 : CollatzResearch.WordTrace tailWord_7631493 prefixEnd_7631493 3918624020422415482240909 := by
  unfold tailWord_7631493
  simp only [CollatzResearch.WordTrace]
  refine ⟨278343416541411691084099133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185562277694274460722732755 278343416541411691084099133)
  ·
    refine ⟨104378781203029384156537175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278343416541411691084099133 104378781203029384156537175)
    ·
      refine ⟨156568171804544076234805763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104378781203029384156537175 156568171804544076234805763)
      ·
        refine ⟨234852257706816114352208645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156568171804544076234805763 234852257706816114352208645)
        ·
          refine ⟨44034798320028021441039121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234852257706816114352208645 44034798320028021441039121)
          ·
            refine ⟨33026098740021016080779341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44034798320028021441039121 33026098740021016080779341)
            ·
              refine ⟨12384787027507881030292253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33026098740021016080779341 12384787027507881030292253)
              ·
                refine ⟨4644295135315455386359595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12384787027507881030292253 4644295135315455386359595)
                ·
                  refine ⟨6966442702973183079539393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644295135315455386359595 6966442702973183079539393)
                  ·
                    refine ⟨5224832027229887309654545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6966442702973183079539393 5224832027229887309654545)
                    ·
                      refine ⟨3918624020422415482240909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224832027229887309654545 3918624020422415482240909)
                      ·
                        rfl

theorem cell23_7631493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_7631493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631493 prefixEnd_7631493 := by exact prefixLift 7631493
  have htrace : WordTrace (prefixWord ++ tailWord_7631493) baseStart_7631493 baseEnd_7631493 := by
    simpa [prefixWord, tailWord_7631493, baseEnd_7631493] using wordTrace_append hprefix tailTrace_7631493
  have hstable : (prefixWord ++ tailWord_7631493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631493).length < 2 ^ (prefixWord ++ tailWord_7631493).sum := by decide
  have hdescent : baseEnd_7631493 < baseStart_7631493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631515 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_7631515 : Nat := 118140960795 + 7631515 * 2 ^ 59
def prefixEnd_7631515 : Nat := 4983230072969 + 3 ^ 40 * 7631515 * 2
def baseEnd_7631515 : Nat := 3918635316996814396165807

theorem tailTrace_7631515 : CollatzResearch.WordTrace tailWord_7631515 prefixEnd_7631515 3918635316996814396165807 := by
  unfold tailWord_7631515
  simp only [CollatzResearch.WordTrace]
  refine ⟨278344218947331988841399999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185562812631554659227599999 278344218947331988841399999)
  ·
    refine ⟨417516328420997983262099999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278344218947331988841399999 417516328420997983262099999)
    ·
      refine ⟨626274492631496974893149999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417516328420997983262099999 626274492631496974893149999)
      ·
        refine ⟨939411738947245462339724999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626274492631496974893149999 939411738947245462339724999)
        ·
          refine ⟨1409117608420868193509587499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939411738947245462339724999 1409117608420868193509587499)
          ·
            refine ⟨2113676412631302290264381249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409117608420868193509587499 2113676412631302290264381249)
            ·
              refine ⟨1585257309473476717698285937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113676412631302290264381249 1585257309473476717698285937)
              ·
                refine ⟨1188942982105107538273714453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585257309473476717698285937 1188942982105107538273714453)
                ·
                  refine ⟨55731702286176915856580365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1188942982105107538273714453 55731702286176915856580365)
                  ·
                    refine ⟨20899388357316343446217637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55731702286176915856580365 20899388357316343446217637)
                    ·
                      refine ⟨3918635316996814396165807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20899388357316343446217637 3918635316996814396165807)
                      ·
                        rfl

theorem cell23_7631515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_7631515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631515 prefixEnd_7631515 := by exact prefixLift 7631515
  have htrace : WordTrace (prefixWord ++ tailWord_7631515) baseStart_7631515 baseEnd_7631515 := by
    simpa [prefixWord, tailWord_7631515, baseEnd_7631515] using wordTrace_append hprefix tailTrace_7631515
  have hstable : (prefixWord ++ tailWord_7631515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631515).length < 2 ^ (prefixWord ++ tailWord_7631515).sum := by decide
  have hdescent : baseEnd_7631515 < baseStart_7631515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631525 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_7631525 : Nat := 118140960795 + 7631525 * 2 ^ 59
def prefixEnd_7631525 : Nat := 4983230072969 + 3 ^ 40 * 7631525 * 2
def baseEnd_7631525 : Nat := 1306213483934453119013587

theorem tailTrace_7631525 : CollatzResearch.WordTrace tailWord_7631525 prefixEnd_7631525 1306213483934453119013587 := by
  unfold tailWord_7631525
  simp only [CollatzResearch.WordTrace]
  refine ⟨278344583677295760549264029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185563055784863840366176019 278344583677295760549264029)
  ·
    refine ⟨104379218878985910205974011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278344583677295760549264029 104379218878985910205974011)
    ·
      refine ⟨156568828318478865308961017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104379218878985910205974011 156568828318478865308961017)
      ·
        refine ⟨117426621238859148981720763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156568828318478865308961017 117426621238859148981720763)
        ·
          refine ⟨176139931858288723472581145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117426621238859148981720763 176139931858288723472581145)
          ·
            refine ⟨132104948893716542604435859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176139931858288723472581145 132104948893716542604435859)
            ·
              refine ⟨198157423340574813906653789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132104948893716542604435859 198157423340574813906653789)
              ·
                refine ⟨74309033752715555214995171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198157423340574813906653789 74309033752715555214995171)
                ·
                  refine ⟨111463550629073332822492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74309033752715555214995171 111463550629073332822492757)
                  ·
                    refine ⟨1306213483934453119013587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111463550629073332822492757 1306213483934453119013587)
                    ·
                      rfl

theorem cell23_7631525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_7631525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631525 prefixEnd_7631525 := by exact prefixLift 7631525
  have htrace : WordTrace (prefixWord ++ tailWord_7631525) baseStart_7631525 baseEnd_7631525 := by
    simpa [prefixWord, tailWord_7631525, baseEnd_7631525] using wordTrace_append hprefix tailTrace_7631525
  have hstable : (prefixWord ++ tailWord_7631525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631525).length < 2 ^ (prefixWord ++ tailWord_7631525).sum := by decide
  have hdescent : baseEnd_7631525 < baseStart_7631525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631530 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7631530 : Nat := 118140960795 + 7631530 * 2 ^ 59
def prefixEnd_7631530 : Nat := 4983230072969 + 3 ^ 40 * 7631530 * 2
def baseEnd_7631530 : Nat := 3918643019206631837478239

theorem tailTrace_7631530 : CollatzResearch.WordTrace tailWord_7631530 prefixEnd_7631530 3918643019206631837478239 := by
  unfold tailWord_7631530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69586191510569411600799011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185563177361518430935464029 69586191510569411600799011)
  ·
    refine ⟨104379287265854117401198517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69586191510569411600799011 104379287265854117401198517)
    ·
      refine ⟨9785558181173823506362361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104379287265854117401198517 9785558181173823506362361)
      ·
        refine ⟨7339168635880367629771771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9785558181173823506362361 7339168635880367629771771)
        ·
          refine ⟨11008752953820551444657657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7339168635880367629771771 11008752953820551444657657)
          ·
            refine ⟨8256564715365413583493243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11008752953820551444657657 8256564715365413583493243)
            ·
              refine ⟨12384847073048120375239865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256564715365413583493243 12384847073048120375239865)
              ·
                refine ⟨9288635304786090281429899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12384847073048120375239865 9288635304786090281429899)
                ·
                  refine ⟨13932952957179135422144849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288635304786090281429899 13932952957179135422144849)
                  ·
                    refine ⟨10449714717884351566608637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13932952957179135422144849 10449714717884351566608637)
                    ·
                      refine ⟨3918643019206631837478239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10449714717884351566608637 3918643019206631837478239)
                      ·
                        rfl

theorem cell23_7631530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7631530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631530 prefixEnd_7631530 := by exact prefixLift 7631530
  have htrace : WordTrace (prefixWord ++ tailWord_7631530) baseStart_7631530 baseEnd_7631530 := by
    simpa [prefixWord, tailWord_7631530, baseEnd_7631530] using wordTrace_append hprefix tailTrace_7631530
  have hstable : (prefixWord ++ tailWord_7631530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631530).length < 2 ^ (prefixWord ++ tailWord_7631530).sum := by decide
  have hdescent : baseEnd_7631530 < baseStart_7631530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631549 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7631549 : Nat := 118140960795 + 7631549 * 2 ^ 59
def prefixEnd_7631549 : Nat := 4983230072969 + 3 ^ 40 * 7631549 * 2
def baseEnd_7631549 : Nat := 3918652775339067263140651

theorem tailTrace_7631549 : CollatzResearch.WordTrace tailWord_7631549 prefixEnd_7631549 3918652775339067263140651 := by
  unfold tailWord_7631549
  simp only [CollatzResearch.WordTrace]
  refine ⟨278345459029208812648137701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185563639352805875098758467 278345459029208812648137701)
  ·
    refine ⟨52189773567976652371525819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278345459029208812648137701 52189773567976652371525819)
    ·
      refine ⟨78284660351964978557288729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52189773567976652371525819 78284660351964978557288729)
      ·
        refine ⟨58713495263973733917966547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78284660351964978557288729 58713495263973733917966547)
        ·
          refine ⟨88070242895960600876949821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58713495263973733917966547 88070242895960600876949821)
          ·
            refine ⟨33026341085985225328856183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88070242895960600876949821 33026341085985225328856183)
            ·
              refine ⟨49539511628977837993284275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33026341085985225328856183 49539511628977837993284275)
              ·
                refine ⟨74309267443466756989926413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49539511628977837993284275 74309267443466756989926413)
                ·
                  refine ⟨27865975291300033871222405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74309267443466756989926413 27865975291300033871222405)
                  ·
                    refine ⟨5224870367118756350854201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27865975291300033871222405 5224870367118756350854201)
                    ·
                      refine ⟨3918652775339067263140651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224870367118756350854201 3918652775339067263140651)
                      ·
                        rfl

theorem cell23_7631549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7631549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631549 prefixEnd_7631549 := by exact prefixLift 7631549
  have htrace : WordTrace (prefixWord ++ tailWord_7631549) baseStart_7631549 baseEnd_7631549 := by
    simpa [prefixWord, tailWord_7631549, baseEnd_7631549] using wordTrace_append hprefix tailTrace_7631549
  have hstable : (prefixWord ++ tailWord_7631549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631549).length < 2 ^ (prefixWord ++ tailWord_7631549).sum := by decide
  have hdescent : baseEnd_7631549 < baseStart_7631549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631552 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_7631552 : Nat := 118140960795 + 7631552 * 2 ^ 59
def prefixEnd_7631552 : Nat := 4983230072969 + 3 ^ 40 * 7631552 * 2
def baseEnd_7631552 : Nat := 3918654315781030751403137

theorem tailTrace_7631552 : CollatzResearch.WordTrace tailWord_7631552 prefixEnd_7631552 3918654315781030751403137 := by
  unfold tailWord_7631552
  simp only [CollatzResearch.WordTrace]
  refine ⟨139172784224098972080248455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185563712298798629440331273 139172784224098972080248455)
  ·
    refine ⟨208759176336148458120372683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139172784224098972080248455 208759176336148458120372683)
    ·
      refine ⟨313138764504222687180559025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208759176336148458120372683 313138764504222687180559025)
      ·
        refine ⟨234854073378167015385419269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313138764504222687180559025 234854073378167015385419269)
        ·
          refine ⟨44035138758406315384766113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234854073378167015385419269 44035138758406315384766113)
          ·
            refine ⟨33026354068804736538574585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44035138758406315384766113 33026354068804736538574585)
            ·
              refine ⟨24769765551603552403930939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33026354068804736538574585 24769765551603552403930939)
              ·
                refine ⟨37154648327405328605896409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24769765551603552403930939 37154648327405328605896409)
                ·
                  refine ⟨27865986245553996454422307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37154648327405328605896409 27865986245553996454422307)
                  ·
                    refine ⟨41798979368330994681633461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27865986245553996454422307 41798979368330994681633461)
                    ·
                      refine ⟨3918654315781030751403137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41798979368330994681633461 3918654315781030751403137)
                      ·
                        rfl

theorem cell23_7631552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_7631552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631552 prefixEnd_7631552 := by exact prefixLift 7631552
  have htrace : WordTrace (prefixWord ++ tailWord_7631552) baseStart_7631552 baseEnd_7631552 := by
    simpa [prefixWord, tailWord_7631552, baseEnd_7631552] using wordTrace_append hprefix tailTrace_7631552
  have hstable : (prefixWord ++ tailWord_7631552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631552).length < 2 ^ (prefixWord ++ tailWord_7631552).sum := by decide
  have hdescent : baseEnd_7631552 < baseStart_7631552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631604 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7631604 : Nat := 118140960795 + 7631604 * 2 ^ 59
def prefixEnd_7631604 : Nat := 4983230072969 + 3 ^ 40 * 7631604 * 2
def baseEnd_7631604 : Nat := 3918681016775064547952899

theorem tailTrace_7631604 : CollatzResearch.WordTrace tailWord_7631604 prefixEnd_7631604 3918681016775064547952899 := by
  unfold tailWord_7631604
  simp only [CollatzResearch.WordTrace]
  refine ⟨139173732522004778520694933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185564976696006371360926577 139173732522004778520694933)
  ·
    refine ⟨6523768711968973993157575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139173732522004778520694933 6523768711968973993157575)
    ·
      refine ⟨9785653067953460989736363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6523768711968973993157575 9785653067953460989736363)
      ·
        refine ⟨14678479601930191484604545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785653067953460989736363 14678479601930191484604545)
        ·
          refine ⟨11008859701447643613453409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14678479601930191484604545 11008859701447643613453409)
          ·
            refine ⟨8256644776085732710090057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11008859701447643613453409 8256644776085732710090057)
            ·
              refine ⟨6192483582064299532567543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8256644776085732710090057 6192483582064299532567543)
              ·
                refine ⟨9288725373096449298851315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192483582064299532567543 9288725373096449298851315)
                ·
                  refine ⟨13933088059644673948276973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288725373096449298851315 13933088059644673948276973)
                  ·
                    refine ⟨5224908022366752730603865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13933088059644673948276973 5224908022366752730603865)
                    ·
                      refine ⟨3918681016775064547952899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224908022366752730603865 3918681016775064547952899)
                      ·
                        rfl

theorem cell23_7631604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7631604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631604 prefixEnd_7631604 := by exact prefixLift 7631604
  have htrace : WordTrace (prefixWord ++ tailWord_7631604) baseStart_7631604 baseEnd_7631604 := by
    simpa [prefixWord, tailWord_7631604, baseEnd_7631604] using wordTrace_append hprefix tailTrace_7631604
  have hstable : (prefixWord ++ tailWord_7631604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631604).length < 2 ^ (prefixWord ++ tailWord_7631604).sum := by decide
  have hdescent : baseEnd_7631604 < baseStart_7631604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631606 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_7631606 : Nat := 118140960795 + 7631606 * 2 ^ 59
def prefixEnd_7631606 : Nat := 4983230072969 + 3 ^ 40 * 7631606 * 2
def baseEnd_7631606 : Nat := 435409115970708171125321

theorem tailTrace_7631606 : CollatzResearch.WordTrace tailWord_7631606 prefixEnd_7631606 435409115970708171125321 := by
  unfold tailWord_7631606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396721124375144461435167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185565025326668207588641781 17396721124375144461435167)
  ·
    refine ⟨26095081686562716692152751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17396721124375144461435167 26095081686562716692152751)
    ·
      refine ⟨39142622529844075038229127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26095081686562716692152751 39142622529844075038229127)
      ·
        refine ⟨58713933794766112557343691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39142622529844075038229127 58713933794766112557343691)
        ·
          refine ⟨88070900692149168836015537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58713933794766112557343691 88070900692149168836015537)
          ·
            refine ⟨66053175519111876627011653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88070900692149168836015537 66053175519111876627011653)
            ·
              refine ⟨12384970409833476867564685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66053175519111876627011653 12384970409833476867564685)
              ·
                refine ⟨4644363903687553825336757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12384970409833476867564685 4644363903687553825336757)
                ·
                  refine ⟨435409115970708171125321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4644363903687553825336757 435409115970708171125321)
                  ·
                    rfl

theorem cell23_7631606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_7631606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631606 prefixEnd_7631606 := by exact prefixLift 7631606
  have htrace : WordTrace (prefixWord ++ tailWord_7631606) baseStart_7631606 baseEnd_7631606 := by
    simpa [prefixWord, tailWord_7631606, baseEnd_7631606] using wordTrace_append hprefix tailTrace_7631606
  have hstable : (prefixWord ++ tailWord_7631606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631606).length < 2 ^ (prefixWord ++ tailWord_7631606).sum := by decide
  have hdescent : baseEnd_7631606 < baseStart_7631606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631649 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_7631649 : Nat := 118140960795 + 7631649 * 2 ^ 59
def prefixEnd_7631649 : Nat := 4983230072969 + 3 ^ 40 * 7631649 * 2
def baseEnd_7631649 : Nat := 1306234707801505623963397

theorem tailTrace_7631649 : CollatzResearch.WordTrace tailWord_7631649 prefixEnd_7631649 1306234707801505623963397 := by
  unfold tailWord_7631649
  simp only [CollatzResearch.WordTrace]
  refine ⟨278349106328846529726778001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185566070885897686484518667 278349106328846529726778001)
  ·
    refine ⟨208761829746634897295083501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278349106328846529726778001 208761829746634897295083501)
    ·
      refine ⟨78285686154988086485656313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208761829746634897295083501 78285686154988086485656313)
      ·
        refine ⟨58714264616241064864242235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78285686154988086485656313 58714264616241064864242235)
        ·
          refine ⟨88071396924361597296363353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58714264616241064864242235 88071396924361597296363353)
          ·
            refine ⟨66053547693271197972272515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88071396924361597296363353 66053547693271197972272515)
            ·
              refine ⟨99080321539906796958408773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66053547693271197972272515 99080321539906796958408773)
              ·
                refine ⟨18577560288732524429701645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99080321539906796958408773 18577560288732524429701645)
                ·
                  refine ⟨6966585108274696661138117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18577560288732524429701645 6966585108274696661138117)
                  ·
                    refine ⟨1306234707801505623963397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966585108274696661138117 1306234707801505623963397)
                    ·
                      rfl

theorem cell23_7631649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_7631649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631649 prefixEnd_7631649 := by exact prefixLift 7631649
  have htrace : WordTrace (prefixWord ++ tailWord_7631649) baseStart_7631649 baseEnd_7631649 := by
    simpa [prefixWord, tailWord_7631649, baseEnd_7631649] using wordTrace_append hprefix tailTrace_7631649
  have hstable : (prefixWord ++ tailWord_7631649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631649).length < 2 ^ (prefixWord ++ tailWord_7631649).sum := by decide
  have hdescent : baseEnd_7631649 < baseStart_7631649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631683 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 1, 4]
def baseStart_7631683 : Nat := 118140960795 + 7631683 * 2 ^ 59
def prefixEnd_7631683 : Nat := 4983230072969 + 3 ^ 40 * 7631683 * 2
def baseEnd_7631683 : Nat := 1306240527248923246288345

theorem tailTrace_7631683 : CollatzResearch.WordTrace tailWord_7631683 prefixEnd_7631683 1306240527248923246288345 := by
  unfold tailWord_7631683
  simp only [CollatzResearch.WordTrace]
  refine ⟨278350346410723353533515703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185566897607148902355677135 278350346410723353533515703)
  ·
    refine ⟨417525519616085030300273555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278350346410723353533515703 417525519616085030300273555)
    ·
      refine ⟨626288279424127545450410333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417525519616085030300273555 626288279424127545450410333)
      ·
        refine ⟨234858104784047829543903875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626288279424127545450410333 234858104784047829543903875)
        ·
          refine ⟨352287157176071744315855813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234858104784047829543903875 352287157176071744315855813)
          ·
            refine ⟨66053841970513452059222965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352287157176071744315855813 66053841970513452059222965)
            ·
              refine ⟨6192547684735636130552153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66053841970513452059222965 6192547684735636130552153)
              ·
                refine ⟨4644410763551727097914115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192547684735636130552153 4644410763551727097914115)
                ·
                  refine ⟨6966616145327590646871173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644410763551727097914115 6966616145327590646871173)
                  ·
                    refine ⟨1306240527248923246288345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966616145327590646871173 1306240527248923246288345)
                    ·
                      rfl

theorem cell23_7631683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 4].length) (baseStart_7631683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631683 prefixEnd_7631683 := by exact prefixLift 7631683
  have htrace : WordTrace (prefixWord ++ tailWord_7631683) baseStart_7631683 baseEnd_7631683 := by
    simpa [prefixWord, tailWord_7631683, baseEnd_7631683] using wordTrace_append hprefix tailTrace_7631683
  have hstable : (prefixWord ++ tailWord_7631683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631683).length < 2 ^ (prefixWord ++ tailWord_7631683).sum := by decide
  have hdescent : baseEnd_7631683 < baseStart_7631683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631699 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 5, 2]
def baseStart_7631699 : Nat := 118140960795 + 7631699 * 2 ^ 59
def prefixEnd_7631699 : Nat := 4983230072969 + 3 ^ 40 * 7631699 * 2
def baseEnd_7631699 : Nat := 3918729797437241676264961

theorem tailTrace_7631699 : CollatzResearch.WordTrace tailWord_7631699 prefixEnd_7631699 3918729797437241676264961 := by
  unfold tailWord_7631699
  simp only [CollatzResearch.WordTrace]
  refine ⟨278350929978665388266098151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185567286652443592177398767 278350929978665388266098151)
  ·
    refine ⟨417526394967998082399147227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278350929978665388266098151 417526394967998082399147227)
    ·
      refine ⟨626289592451997123598720841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417526394967998082399147227 626289592451997123598720841)
      ·
        refine ⟨469717194338997842699040631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626289592451997123598720841 469717194338997842699040631)
        ·
          refine ⟨704575791508496764048560947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469717194338997842699040631 704575791508496764048560947)
          ·
            refine ⟨1056863687262745146072841421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704575791508496764048560947 1056863687262745146072841421)
            ·
              refine ⟨396323882723529429777315533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056863687262745146072841421 396323882723529429777315533)
              ·
                refine ⟨148621456021323536166493325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396323882723529429777315533 148621456021323536166493325)
                ·
                  refine ⟨55733046007996326062434997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148621456021323536166493325 55733046007996326062434997)
                  ·
                    refine ⟨5224973063249655568353281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55733046007996326062434997 5224973063249655568353281)
                    ·
                      refine ⟨3918729797437241676264961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224973063249655568353281 3918729797437241676264961)
                      ·
                        rfl

theorem cell23_7631699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5, 2].length) (baseStart_7631699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631699 prefixEnd_7631699 := by exact prefixLift 7631699
  have htrace : WordTrace (prefixWord ++ tailWord_7631699) baseStart_7631699 baseEnd_7631699 := by
    simpa [prefixWord, tailWord_7631699, baseEnd_7631699] using wordTrace_append hprefix tailTrace_7631699
  have hstable : (prefixWord ++ tailWord_7631699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631699).length < 2 ^ (prefixWord ++ tailWord_7631699).sum := by decide
  have hdescent : baseEnd_7631699 < baseStart_7631699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631733 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7631733 : Nat := 118140960795 + 7631733 * 2 ^ 59
def prefixEnd_7631733 : Nat := 4983230072969 + 3 ^ 40 * 7631733 * 2
def baseEnd_7631733 : Nat := 3918747255779494543239805

theorem tailTrace_7631733 : CollatzResearch.WordTrace tailWord_7631733 prefixEnd_7631733 3918747255779494543239805 := by
  unfold tailWord_7631733
  simp only [CollatzResearch.WordTrace]
  refine ⟨278352170060542212072835853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185568113373694808048557235 278352170060542212072835853)
  ·
    refine ⟨104382063772703329527313445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278352170060542212072835853 104382063772703329527313445)
    ·
      refine ⟨19571636957381874286371271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104382063772703329527313445 19571636957381874286371271)
      ·
        refine ⟨29357455436072811429556907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19571636957381874286371271 29357455436072811429556907)
        ·
          refine ⟨44036183154109217144335361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29357455436072811429556907 44036183154109217144335361)
          ·
            refine ⟨33027137365581912858251521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44036183154109217144335361 33027137365581912858251521)
            ·
              refine ⟨24770353024186434643688641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33027137365581912858251521 24770353024186434643688641)
              ·
                refine ⟨18577764768139825982766481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24770353024186434643688641 18577764768139825982766481)
                ·
                  refine ⟨13933323576104869487074861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18577764768139825982766481 13933323576104869487074861)
                  ·
                    refine ⟨5224996341039326057653073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13933323576104869487074861 5224996341039326057653073)
                    ·
                      refine ⟨3918747255779494543239805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5224996341039326057653073 3918747255779494543239805)
                      ·
                        rfl

theorem cell23_7631733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7631733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631733 prefixEnd_7631733 := by exact prefixLift 7631733
  have htrace : WordTrace (prefixWord ++ tailWord_7631733) baseStart_7631733 baseEnd_7631733 := by
    simpa [prefixWord, tailWord_7631733, baseEnd_7631733] using wordTrace_append hprefix tailTrace_7631733
  have hstable : (prefixWord ++ tailWord_7631733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631733).length < 2 ^ (prefixWord ++ tailWord_7631733).sum := by decide
  have hdescent : baseEnd_7631733 < baseStart_7631733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631739 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 4, 4]
def baseStart_7631739 : Nat := 118140960795 + 7631739 * 2 ^ 59
def prefixEnd_7631739 : Nat := 4983230072969 + 3 ^ 40 * 7631739 * 2
def baseEnd_7631739 : Nat := 1306250112221140506588259

theorem tailTrace_7631739 : CollatzResearch.WordTrace tailWord_7631739 prefixEnd_7631739 1306250112221140506588259 := by
  unfold tailWord_7631739
  simp only [CollatzResearch.WordTrace]
  refine ⟨278352388898520475097554271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185568259265680316731702847 278352388898520475097554271)
  ·
    refine ⟨417528583347780712646331407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278352388898520475097554271 417528583347780712646331407)
    ·
      refine ⟨626292875021671068969497111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417528583347780712646331407 626292875021671068969497111)
      ·
        refine ⟨939439312532506603454245667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626292875021671068969497111 939439312532506603454245667)
        ·
          refine ⟨1409158968798759905181368501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939439312532506603454245667 1409158968798759905181368501)
          ·
            refine ⟨132108653324883741110753297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1409158968798759905181368501 132108653324883741110753297)
            ·
              refine ⟨99081489993662805833064973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132108653324883741110753297 99081489993662805833064973)
              ·
                refine ⟨37155558747623552187399365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99081489993662805833064973 37155558747623552187399365)
                ·
                  refine ⟨6966667265179416035137381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37155558747623552187399365 6966667265179416035137381)
                  ·
                    refine ⟨1306250112221140506588259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966667265179416035137381 1306250112221140506588259)
                    ·
                      rfl

theorem cell23_7631739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 4].length) (baseStart_7631739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631739 prefixEnd_7631739 := by exact prefixLift 7631739
  have htrace : WordTrace (prefixWord ++ tailWord_7631739) baseStart_7631739 baseEnd_7631739 := by
    simpa [prefixWord, tailWord_7631739, baseEnd_7631739] using wordTrace_append hprefix tailTrace_7631739
  have hstable : (prefixWord ++ tailWord_7631739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631739).length < 2 ^ (prefixWord ++ tailWord_7631739).sum := by decide
  have hdescent : baseEnd_7631739 < baseStart_7631739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631756 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_7631756 : Nat := 118140960795 + 7631756 * 2 ^ 59
def prefixEnd_7631756 : Nat := 4983230072969 + 3 ^ 40 * 7631756 * 2
def baseEnd_7631756 : Nat := 1306253021944849317750733

theorem tailTrace_7631756 : CollatzResearch.WordTrace tailWord_7631756 prefixEnd_7631756 1306253021944849317750733 := by
  unfold tailWord_7631756
  simp only [CollatzResearch.WordTrace]
  refine ⟨139176504469729443500461561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185568672626305924667282081 139176504469729443500461561)
  ·
    refine ⟨104382378352297082625346171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139176504469729443500461561 104382378352297082625346171)
    ·
      refine ⟨156573567528445623938019257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104382378352297082625346171 156573567528445623938019257)
      ·
        refine ⟨117430175646334217953514443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156573567528445623938019257 117430175646334217953514443)
        ·
          refine ⟨176145263469501326930271665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117430175646334217953514443 176145263469501326930271665)
          ·
            refine ⟨132108947602125995197703749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176145263469501326930271665 132108947602125995197703749)
            ·
              refine ⟨24770427675398624099569453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132108947602125995197703749 24770427675398624099569453)
              ·
                refine ⟨9288910378274484037338545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24770427675398624099569453 9288910378274484037338545)
                ·
                  refine ⟨6966682783705863028003909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9288910378274484037338545 6966682783705863028003909)
                  ·
                    refine ⟨1306253021944849317750733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966682783705863028003909 1306253021944849317750733)
                    ·
                      rfl

theorem cell23_7631756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_7631756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631756 prefixEnd_7631756 := by exact prefixLift 7631756
  have htrace : WordTrace (prefixWord ++ tailWord_7631756) baseStart_7631756 baseEnd_7631756 := by
    simpa [prefixWord, tailWord_7631756, baseEnd_7631756] using wordTrace_append hprefix tailTrace_7631756
  have hstable : (prefixWord ++ tailWord_7631756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631756).length < 2 ^ (prefixWord ++ tailWord_7631756).sum := by decide
  have hdescent : baseEnd_7631756 < baseStart_7631756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631823 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 1, 3, 2]
def baseStart_7631823 : Nat := 118140960795 + 7631823 * 2 ^ 59
def prefixEnd_7631823 : Nat := 4983230072969 + 3 ^ 40 * 7631823 * 2
def baseEnd_7631823 : Nat := 3918793469038399191114391

theorem tailTrace_7631823 : CollatzResearch.WordTrace tailWord_7631823 prefixEnd_7631823 3918793469038399191114391 := by
  unfold tailWord_7631823
  simp only [CollatzResearch.WordTrace]
  refine ⟨278355452630216157443612123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185570301753477438295741415 278355452630216157443612123)
  ·
    refine ⟨417533178945324236165418185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278355452630216157443612123 417533178945324236165418185)
    ·
      refine ⟨313149884208993177124063639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417533178945324236165418185 313149884208993177124063639)
      ·
        refine ⟨469724826313489765686095459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313149884208993177124063639 469724826313489765686095459)
        ·
          refine ⟨704587239470234648529143189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469724826313489765686095459 704587239470234648529143189)
          ·
            refine ⟨33027526850167249149803587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 704587239470234648529143189 33027526850167249149803587)
            ·
              refine ⟨49541290275250873724705381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33027526850167249149803587 49541290275250873724705381)
              ·
                refine ⟨9288991926609538823382259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49541290275250873724705381 9288991926609538823382259)
                ·
                  refine ⟨13933487889914308235073389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288991926609538823382259 13933487889914308235073389)
                  ·
                    refine ⟨5225057958717865588152521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13933487889914308235073389 5225057958717865588152521)
                    ·
                      refine ⟨3918793469038399191114391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225057958717865588152521 3918793469038399191114391)
                      ·
                        rfl

theorem cell23_7631823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 3, 2].length) (baseStart_7631823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631823 prefixEnd_7631823 := by exact prefixLift 7631823
  have htrace : WordTrace (prefixWord ++ tailWord_7631823) baseStart_7631823 baseEnd_7631823 := by
    simpa [prefixWord, tailWord_7631823, baseEnd_7631823] using wordTrace_append hprefix tailTrace_7631823
  have hstable : (prefixWord ++ tailWord_7631823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631823).length < 2 ^ (prefixWord ++ tailWord_7631823).sum := by decide
  have hdescent : baseEnd_7631823 < baseStart_7631823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631826 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_7631826 : Nat := 118140960795 + 7631826 * 2 ^ 59
def prefixEnd_7631826 : Nat := 4983230072969 + 3 ^ 40 * 7631826 * 2
def baseEnd_7631826 : Nat := 3918795009480362679376877

theorem tailTrace_7631826 : CollatzResearch.WordTrace tailWord_7631826 prefixEnd_7631826 3918795009480362679376877 := by
  unfold tailWord_7631826
  simp only [CollatzResearch.WordTrace]
  refine ⟨69588890512301322238992833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185570374699470192637314221 69588890512301322238992833)
  ·
    refine ⟨52191667884225991679244625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69588890512301322238992833 52191667884225991679244625)
    ·
      refine ⟨39143750913169493759433469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52191667884225991679244625 39143750913169493759433469)
      ·
        refine ⟨14678906592438560159787551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39143750913169493759433469 14678906592438560159787551)
        ·
          refine ⟨22018359888657840239681327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14678906592438560159787551 22018359888657840239681327)
          ·
            refine ⟨33027539832986760359521991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22018359888657840239681327 33027539832986760359521991)
            ·
              refine ⟨49541309749480140539282987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33027539832986760359521991 49541309749480140539282987)
              ·
                refine ⟨74311964624220210808924481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49541309749480140539282987 74311964624220210808924481)
                ·
                  refine ⟨55733973468165158106693361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74311964624220210808924481 55733973468165158106693361)
                  ·
                    refine ⟨41800480101123868580020021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55733973468165158106693361 41800480101123868580020021)
                    ·
                      refine ⟨3918795009480362679376877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41800480101123868580020021 3918795009480362679376877)
                      ·
                        rfl

theorem cell23_7631826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_7631826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631826 prefixEnd_7631826 := by exact prefixLift 7631826
  have htrace : WordTrace (prefixWord ++ tailWord_7631826) baseStart_7631826 baseEnd_7631826 := by
    simpa [prefixWord, tailWord_7631826, baseEnd_7631826] using wordTrace_append hprefix tailTrace_7631826
  have hstable : (prefixWord ++ tailWord_7631826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631826).length < 2 ^ (prefixWord ++ tailWord_7631826).sum := by decide
  have hdescent : baseEnd_7631826 < baseStart_7631826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631830 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7631830 : Nat := 118140960795 + 7631830 * 2 ^ 59
def prefixEnd_7631830 : Nat := 4983230072969 + 3 ^ 40 * 7631830 * 2
def baseEnd_7631830 : Nat := 3918797063402980663726859

theorem tailTrace_7631830 : CollatzResearch.WordTrace tailWord_7631830 prefixEnd_7631830 3918797063402980663726859 := by
  unfold tailWord_7631830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17397231746324424852444809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185570471960793865092744629 17397231746324424852444809)
  ·
    refine ⟨13047923809743318639333607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17397231746324424852444809 13047923809743318639333607)
    ·
      refine ⟨19571885714614977959000411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13047923809743318639333607 19571885714614977959000411)
      ·
        refine ⟨29357828571922466938500617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19571885714614977959000411 29357828571922466938500617)
        ·
          refine ⟨22018371428941850203875463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29357828571922466938500617 22018371428941850203875463)
          ·
            refine ⟨33027557143412775305813195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22018371428941850203875463 33027557143412775305813195)
            ·
              refine ⟨49541335715119162958719793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33027557143412775305813195 49541335715119162958719793)
              ·
                refine ⟨37156001786339372219039845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49541335715119162958719793 37156001786339372219039845)
                ·
                  refine ⟨6966750334938632291069971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37156001786339372219039845 6966750334938632291069971)
                  ·
                    refine ⟨10450125502407948436604957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966750334938632291069971 10450125502407948436604957)
                    ·
                      refine ⟨3918797063402980663726859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10450125502407948436604957 3918797063402980663726859)
                      ·
                        rfl

theorem cell23_7631830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7631830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631830 prefixEnd_7631830 := by exact prefixLift 7631830
  have htrace : WordTrace (prefixWord ++ tailWord_7631830) baseStart_7631830 baseEnd_7631830 := by
    simpa [prefixWord, tailWord_7631830, baseEnd_7631830] using wordTrace_append hprefix tailTrace_7631830
  have hstable : (prefixWord ++ tailWord_7631830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631830).length < 2 ^ (prefixWord ++ tailWord_7631830).sum := by decide
  have hdescent : baseEnd_7631830 < baseStart_7631830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631889 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_7631889 : Nat := 118140960795 + 7631889 * 2 ^ 59
def prefixEnd_7631889 : Nat := 4983230072969 + 3 ^ 40 * 7631889 * 2
def baseEnd_7631889 : Nat := 1306275786253865310963029

theorem tailTrace_7631889 : CollatzResearch.WordTrace tailWord_7631889 prefixEnd_7631889 1306275786253865310963029 := by
  unfold tailWord_7631889
  simp only [CollatzResearch.WordTrace]
  refine ⟨278357859847977050715514721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185571906565318033810343147 278357859847977050715514721)
  ·
    refine ⟨208768394885982788036636041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278357859847977050715514721 208768394885982788036636041)
    ·
      refine ⟨156576296164487091027477031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208768394885982788036636041 156576296164487091027477031)
      ·
        refine ⟨234864444246730636541215547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156576296164487091027477031 234864444246730636541215547)
        ·
          refine ⟨352296666370095954811823321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234864444246730636541215547 352296666370095954811823321)
          ·
            refine ⟨264222499777571966108867491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352296666370095954811823321 264222499777571966108867491)
            ·
              refine ⟨396333749666357949163301237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264222499777571966108867491 396333749666357949163301237)
              ·
                refine ⟨37156289031221057734059491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396333749666357949163301237 37156289031221057734059491)
                ·
                  refine ⟨55734433546831586601089237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37156289031221057734059491 55734433546831586601089237)
                  ·
                    refine ⟨1306275786253865310963029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55734433546831586601089237 1306275786253865310963029)
                    ·
                      rfl

theorem cell23_7631889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_7631889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631889 prefixEnd_7631889 := by exact prefixLift 7631889
  have htrace : WordTrace (prefixWord ++ tailWord_7631889) baseStart_7631889 baseEnd_7631889 := by
    simpa [prefixWord, tailWord_7631889, baseEnd_7631889] using wordTrace_append hprefix tailTrace_7631889
  have hstable : (prefixWord ++ tailWord_7631889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631889).length < 2 ^ (prefixWord ++ tailWord_7631889).sum := by decide
  have hdescent : baseEnd_7631889 < baseStart_7631889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631904 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7631904 : Nat := 118140960795 + 7631904 * 2 ^ 59
def prefixEnd_7631904 : Nat := 4983230072969 + 3 ^ 40 * 7631904 * 2
def baseEnd_7631904 : Nat := 3918835060971413374201519

theorem tailTrace_7631904 : CollatzResearch.WordTrace tailWord_7631904 prefixEnd_7631904 3918835060971413374201519 := by
  unfold tailWord_7631904
  simp only [CollatzResearch.WordTrace]
  refine ⟨139179203471461354138655383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185572271295281805518207177 139179203471461354138655383)
  ·
    refine ⟨208768805207192031207983075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139179203471461354138655383 208768805207192031207983075)
    ·
      refine ⟨313153207810788046811974613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208768805207192031207983075 313153207810788046811974613)
      ·
        refine ⟨7339528308065344847155655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 313153207810788046811974613 7339528308065344847155655)
        ·
          refine ⟨11009292462098017270733483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7339528308065344847155655 11009292462098017270733483)
          ·
            refine ⟨16513938693147025906100225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009292462098017270733483 16513938693147025906100225)
            ·
              refine ⟨12385454019860269429575169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16513938693147025906100225 12385454019860269429575169)
              ·
                refine ⟨9289090514895202072181377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12385454019860269429575169 9289090514895202072181377)
                ·
                  refine ⟨6966817886171401554136033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9289090514895202072181377 6966817886171401554136033)
                  ·
                    refine ⟨5225113414628551165602025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6966817886171401554136033 5225113414628551165602025)
                    ·
                      refine ⟨3918835060971413374201519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225113414628551165602025 3918835060971413374201519)
                      ·
                        rfl

theorem cell23_7631904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7631904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631904 prefixEnd_7631904 := by exact prefixLift 7631904
  have htrace : WordTrace (prefixWord ++ tailWord_7631904) baseStart_7631904 baseEnd_7631904 := by
    simpa [prefixWord, tailWord_7631904, baseEnd_7631904] using wordTrace_append hprefix tailTrace_7631904
  have hstable : (prefixWord ++ tailWord_7631904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631904).length < 2 ^ (prefixWord ++ tailWord_7631904).sum := by decide
  have hdescent : baseEnd_7631904 < baseStart_7631904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631943 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_7631943 : Nat := 118140960795 + 7631943 * 2 ^ 59
def prefixEnd_7631943 : Nat := 4983230072969 + 3 ^ 40 * 7631943 * 2
def baseEnd_7631943 : Nat := 3918855086716938721613839

theorem tailTrace_7631943 : CollatzResearch.WordTrace tailWord_7631943 prefixEnd_7631943 3918855086716938721613839 := by
  unfold tailWord_7631943
  simp only [CollatzResearch.WordTrace]
  refine ⟨278359829389781417937980483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185573219593187611958653655 278359829389781417937980483)
  ·
    refine ⟨417539744084672126906970725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278359829389781417937980483 417539744084672126906970725)
    ·
      refine ⟨78288702015876023795057011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417539744084672126906970725 78288702015876023795057011)
      ·
        refine ⟨117433053023814035692585517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78288702015876023795057011 117433053023814035692585517)
        ·
          refine ⟨44037394883930263384719569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117433053023814035692585517 44037394883930263384719569)
          ·
            refine ⟨33028046162947697538539677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44037394883930263384719569 33028046162947697538539677)
            ·
              refine ⟨12385517311105386576952379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33028046162947697538539677 12385517311105386576952379)
              ·
                refine ⟨18578275966658079865428569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12385517311105386576952379 18578275966658079865428569)
                ·
                  refine ⟨13933706974993559899071427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18578275966658079865428569 13933706974993559899071427)
                  ·
                    refine ⟨20900560462490339848607141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13933706974993559899071427 20900560462490339848607141)
                    ·
                      refine ⟨3918855086716938721613839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20900560462490339848607141 3918855086716938721613839)
                      ·
                        rfl

theorem cell23_7631943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_7631943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631943 prefixEnd_7631943 := by exact prefixLift 7631943
  have htrace : WordTrace (prefixWord ++ tailWord_7631943) baseStart_7631943 baseEnd_7631943 := by
    simpa [prefixWord, tailWord_7631943, baseEnd_7631943] using wordTrace_append hprefix tailTrace_7631943
  have hstable : (prefixWord ++ tailWord_7631943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631943).length < 2 ^ (prefixWord ++ tailWord_7631943).sum := by decide
  have hdescent : baseEnd_7631943 < baseStart_7631943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631956 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_7631956 : Nat := 118140960795 + 7631956 * 2 ^ 59
def prefixEnd_7631956 : Nat := 4983230072969 + 3 ^ 40 * 7631956 * 2
def baseEnd_7631956 : Nat := 3918861761965447170751279

theorem tailTrace_7631956 : CollatzResearch.WordTrace tailWord_7631956 prefixEnd_7631956 3918861761965447170751279 := by
  unfold tailWord_7631956
  simp only [CollatzResearch.WordTrace]
  refine ⟨139180151769367160579101861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185573535692489547438802481 139180151769367160579101861)
  ·
    refine ⟨26096278456756342608581599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139180151769367160579101861 26096278456756342608581599)
    ·
      refine ⟨39144417685134513912872399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26096278456756342608581599 39144417685134513912872399)
      ·
        refine ⟨58716626527701770869308599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39144417685134513912872399 58716626527701770869308599)
        ·
          refine ⟨88074939791552656303962899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58716626527701770869308599 88074939791552656303962899)
          ·
            refine ⟨132112409687328984455944349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88074939791552656303962899 132112409687328984455944349)
            ·
              refine ⟨49542153632748369170979131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132112409687328984455944349 49542153632748369170979131)
              ·
                refine ⟨74313230449122553756468697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49542153632748369170979131 74313230449122553756468697)
                ·
                  refine ⟨55734922836841915317351523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74313230449122553756468697 55734922836841915317351523)
                  ·
                    refine ⟨83602384255262872976027285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55734922836841915317351523 83602384255262872976027285)
                    ·
                      refine ⟨3918861761965447170751279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83602384255262872976027285 3918861761965447170751279)
                      ·
                        rfl

theorem cell23_7631956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_7631956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631956 prefixEnd_7631956 := by exact prefixLift 7631956
  have htrace : WordTrace (prefixWord ++ tailWord_7631956) baseStart_7631956 baseEnd_7631956 := by
    simpa [prefixWord, tailWord_7631956, baseEnd_7631956] using wordTrace_append hprefix tailTrace_7631956
  have hstable : (prefixWord ++ tailWord_7631956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631956).length < 2 ^ (prefixWord ++ tailWord_7631956).sum := by decide
  have hdescent : baseEnd_7631956 < baseStart_7631956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631970 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_7631970 : Nat := 118140960795 + 7631970 * 2 ^ 59
def prefixEnd_7631970 : Nat := 4983230072969 + 3 ^ 40 * 7631970 * 2
def baseEnd_7631970 : Nat := 1306289650231536705325405

theorem tailTrace_7631970 : CollatzResearch.WordTrace tailWord_7631970 prefixEnd_7631970 1306289650231536705325405 := by
  unfold tailWord_7631970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590203540170900387303341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185573876107122401032808909 69590203540170900387303341)
  ·
    refine ⟨26096326327564087645238753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69590203540170900387303341 26096326327564087645238753)
    ·
      refine ⟨19572244745673065733929065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26096326327564087645238753 19572244745673065733929065)
      ·
        refine ⟨14679183559254799300446799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19572244745673065733929065 14679183559254799300446799)
        ·
          refine ⟨22018775338882198950670199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679183559254799300446799 22018775338882198950670199)
          ·
            refine ⟨33028163008323298426005299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22018775338882198950670199 33028163008323298426005299)
            ·
              refine ⟨49542244512484947639007949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33028163008323298426005299 49542244512484947639007949)
              ·
                refine ⟨18578341692181855364627981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49542244512484947639007949 18578341692181855364627981)
                ·
                  refine ⟨6966878134568195761735493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18578341692181855364627981 6966878134568195761735493)
                  ·
                    refine ⟨1306289650231536705325405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966878134568195761735493 1306289650231536705325405)
                    ·
                      rfl

theorem cell23_7631970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_7631970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631970 prefixEnd_7631970 := by exact prefixLift 7631970
  have htrace : WordTrace (prefixWord ++ tailWord_7631970) baseStart_7631970 baseEnd_7631970 := by
    simpa [prefixWord, tailWord_7631970, baseEnd_7631970] using wordTrace_append hprefix tailTrace_7631970
  have hstable : (prefixWord ++ tailWord_7631970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631970).length < 2 ^ (prefixWord ++ tailWord_7631970).sum := by decide
  have hdescent : baseEnd_7631970 < baseStart_7631970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631983 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 6]
def baseStart_7631983 : Nat := 118140960795 + 7631983 * 2 ^ 59
def prefixEnd_7631983 : Nat := 4983230072969 + 3 ^ 40 * 7631983 * 2
def baseEnd_7631983 : Nat := 435430625104790951679295

theorem tailTrace_7631983 : CollatzResearch.WordTrace tailWord_7631983 prefixEnd_7631983 435430625104790951679295 := by
  unfold tailWord_7631983
  simp only [CollatzResearch.WordTrace]
  refine ⟨278361288309636504769436603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185574192206424336512957735 278361288309636504769436603)
  ·
    refine ⟨417541932464454757154154905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278361288309636504769436603 417541932464454757154154905)
    ·
      refine ⟨313156449348341067865616179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417541932464454757154154905 313156449348341067865616179)
      ·
        refine ⟨469734674022511601798424269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313156449348341067865616179 469734674022511601798424269)
        ·
          refine ⟨176150502758441850674409101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469734674022511601798424269 176150502758441850674409101)
          ·
            refine ⟨66056438534415694002903413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176150502758441850674409101 66056438534415694002903413)
            ·
              refine ⟨6192791112601471312772195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66056438534415694002903413 6192791112601471312772195)
              ·
                refine ⟨9289186668902206969158293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192791112601471312772195 9289186668902206969158293)
                ·
                  refine ⟨435430625104790951679295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9289186668902206969158293 435430625104790951679295)
                  ·
                    rfl

theorem cell23_7631983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 6].length) (baseStart_7631983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631983 prefixEnd_7631983 := by exact prefixLift 7631983
  have htrace : WordTrace (prefixWord ++ tailWord_7631983) baseStart_7631983 baseEnd_7631983 := by
    simpa [prefixWord, tailWord_7631983, baseEnd_7631983] using wordTrace_append hprefix tailTrace_7631983
  have hstable : (prefixWord ++ tailWord_7631983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631983).length < 2 ^ (prefixWord ++ tailWord_7631983).sum := by decide
  have hdescent : baseEnd_7631983 < baseStart_7631983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7631986 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7631986 : Nat := 118140960795 + 7631986 * 2 ^ 59
def prefixEnd_7631986 : Nat := 4983230072969 + 3 ^ 40 * 7631986 * 2
def baseEnd_7631986 : Nat := 3918877166385082053376141

theorem tailTrace_7631986 : CollatzResearch.WordTrace tailWord_7631986 prefixEnd_7631986 3918877166385082053376141 := by
  unfold tailWord_7631986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590349432156409070448953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185574265152417090854530541 69590349432156409070448953)
  ·
    refine ⟨52192762074117306802836715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69590349432156409070448953 52192762074117306802836715)
    ·
      refine ⟨78289143111175960204255073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52192762074117306802836715 78289143111175960204255073)
      ·
        refine ⟨58716857333381970153191305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78289143111175960204255073 58716857333381970153191305)
        ·
          refine ⟨44037643000036477614893479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58716857333381970153191305 44037643000036477614893479)
          ·
            refine ⟨66056464500054716422340219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44037643000036477614893479 66056464500054716422340219)
            ·
              refine ⟨99084696750082074633510329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66056464500054716422340219 99084696750082074633510329)
              ·
                refine ⟨74313522562561555975132747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99084696750082074633510329 74313522562561555975132747)
                ·
                  refine ⟨111470283843842333962699121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74313522562561555975132747 111470283843842333962699121)
                  ·
                    refine ⟨83602712882881750472024341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111470283843842333962699121 83602712882881750472024341)
                    ·
                      refine ⟨3918877166385082053376141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83602712882881750472024341 3918877166385082053376141)
                      ·
                        rfl

theorem cell23_7631986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7631986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7631986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7631986 prefixEnd_7631986 := by exact prefixLift 7631986
  have htrace : WordTrace (prefixWord ++ tailWord_7631986) baseStart_7631986 baseEnd_7631986 := by
    simpa [prefixWord, tailWord_7631986, baseEnd_7631986] using wordTrace_append hprefix tailTrace_7631986
  have hstable : (prefixWord ++ tailWord_7631986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7631986).length < 2 ^ (prefixWord ++ tailWord_7631986).sum := by decide
  have hdescent : baseEnd_7631986 < baseStart_7631986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7631986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632003 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 5, 2]
def baseStart_7632003 : Nat := 118140960795 + 7632003 * 2 ^ 59
def prefixEnd_7632003 : Nat := 4983230072969 + 3 ^ 40 * 7632003 * 2
def baseEnd_7632003 : Nat := 3918885895556208486863563

theorem tailTrace_7632003 : CollatzResearch.WordTrace tailWord_7632003 prefixEnd_7632003 3918885895556208486863563 := by
  unfold tailWord_7632003
  simp only [CollatzResearch.WordTrace]
  refine ⟨278362017769564048185164663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185574678513042698790109775 278362017769564048185164663)
  ·
    refine ⟨417543026654346072277746995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278362017769564048185164663 417543026654346072277746995)
    ·
      refine ⟨626314539981519108416620493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417543026654346072277746995 626314539981519108416620493)
      ·
        refine ⟨234867952493069665656232685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626314539981519108416620493 234867952493069665656232685)
        ·
          refine ⟨88075482184901124621087257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234867952493069665656232685 88075482184901124621087257)
          ·
            refine ⟨66056611638675843465815443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88075482184901124621087257 66056611638675843465815443)
            ·
              refine ⟨99084917458013765198723165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66056611638675843465815443 99084917458013765198723165)
              ·
                refine ⟨37156844046755161949521187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99084917458013765198723165 37156844046755161949521187)
                ·
                  refine ⟨55735266070132742924281781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37156844046755161949521187 55735266070132742924281781)
                  ·
                    refine ⟨5225181194074944649151417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55735266070132742924281781 5225181194074944649151417)
                    ·
                      refine ⟨3918885895556208486863563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225181194074944649151417 3918885895556208486863563)
                      ·
                        rfl

theorem cell23_7632003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_7632003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632003 prefixEnd_7632003 := by exact prefixLift 7632003
  have htrace : WordTrace (prefixWord ++ tailWord_7632003) baseStart_7632003 baseEnd_7632003 := by
    simpa [prefixWord, tailWord_7632003, baseEnd_7632003] using wordTrace_append hprefix tailTrace_7632003
  have hstable : (prefixWord ++ tailWord_7632003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632003).length < 2 ^ (prefixWord ++ tailWord_7632003).sum := by decide
  have hdescent : baseEnd_7632003 < baseStart_7632003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632033 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7632033 : Nat := 118140960795 + 7632033 * 2 ^ 59
def prefixEnd_7632033 : Nat := 4983230072969 + 3 ^ 40 * 7632033 * 2
def baseEnd_7632033 : Nat := 3918901299975843369488425

theorem tailTrace_7632033 : CollatzResearch.WordTrace tailWord_7632033 prefixEnd_7632033 3918901299975843369488425 := by
  unfold tailWord_7632033
  simp only [CollatzResearch.WordTrace]
  refine ⟨278363111959455363308756753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185575407972970242205837835 278363111959455363308756753)
  ·
    refine ⟨208772333969591522481567565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278363111959455363308756753 208772333969591522481567565)
    ·
      refine ⟨78289625238596820930587837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208772333969591522481567565 78289625238596820930587837)
      ·
        refine ⟨29358609464473807848970439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78289625238596820930587837 29358609464473807848970439)
        ·
          refine ⟨44037914196710711773455659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29358609464473807848970439 44037914196710711773455659)
          ·
            refine ⟨66056871295066067660183489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44037914196710711773455659 66056871295066067660183489)
            ·
              refine ⟨49542653471299550745137617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66056871295066067660183489 49542653471299550745137617)
              ·
                refine ⟨37156990103474663058853213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49542653471299550745137617 37156990103474663058853213)
                ·
                  refine ⟨13933871288802998647069955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37156990103474663058853213 13933871288802998647069955)
                  ·
                    refine ⟨20900806933204497970604933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13933871288802998647069955 20900806933204497970604933)
                    ·
                      refine ⟨3918901299975843369488425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20900806933204497970604933 3918901299975843369488425)
                      ·
                        rfl

theorem cell23_7632033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7632033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632033 prefixEnd_7632033 := by exact prefixLift 7632033
  have htrace : WordTrace (prefixWord ++ tailWord_7632033) baseStart_7632033 baseEnd_7632033 := by
    simpa [prefixWord, tailWord_7632033, baseEnd_7632033] using wordTrace_append hprefix tailTrace_7632033
  have hstable : (prefixWord ++ tailWord_7632033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632033).length < 2 ^ (prefixWord ++ tailWord_7632033).sum := by decide
  have hdescent : baseEnd_7632033 < baseStart_7632033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632034 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_7632034 : Nat := 118140960795 + 7632034 * 2 ^ 59
def prefixEnd_7632034 : Nat := 4983230072969 + 3 ^ 40 * 7632034 * 2
def baseEnd_7632034 : Nat := 435433534828499762841769

theorem tailTrace_7632034 : CollatzResearch.WordTrace tailWord_7632034 prefixEnd_7632034 435433534828499762841769 := by
  unfold tailWord_7632034
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590787108112935119885789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185575432288301160319695437 69590787108112935119885789)
  ·
    refine ⟨26096545165542350669957171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69590787108112935119885789 26096545165542350669957171)
    ·
      refine ⟨39144817748313526004935757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26096545165542350669957171 39144817748313526004935757)
      ·
        refine ⟨14679306655617572251850909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39144817748313526004935757 14679306655617572251850909)
        ·
          refine ⟨5504739995856589594444091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14679306655617572251850909 5504739995856589594444091)
          ·
            refine ⟨8257109993784884391666137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504739995856589594444091 8257109993784884391666137)
            ·
              refine ⟨6192832495338663293749603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8257109993784884391666137 6192832495338663293749603)
              ·
                refine ⟨9289248743007994940624405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192832495338663293749603 9289248743007994940624405)
                ·
                  refine ⟨435433534828499762841769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9289248743007994940624405 435433534828499762841769)
                  ·
                    rfl

theorem cell23_7632034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_7632034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632034 prefixEnd_7632034 := by exact prefixLift 7632034
  have htrace : WordTrace (prefixWord ++ tailWord_7632034) baseStart_7632034 baseEnd_7632034 := by
    simpa [prefixWord, tailWord_7632034, baseEnd_7632034] using wordTrace_append hprefix tailTrace_7632034
  have hstable : (prefixWord ++ tailWord_7632034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632034).length < 2 ^ (prefixWord ++ tailWord_7632034).sum := by decide
  have hdescent : baseEnd_7632034 < baseStart_7632034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632050 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_7632050 : Nat := 118140960795 + 7632050 * 2 ^ 59
def prefixEnd_7632050 : Nat := 4983230072969 + 3 ^ 40 * 7632050 * 2
def baseEnd_7632050 : Nat := 3918910029146969802975847

theorem tailTrace_7632050 : CollatzResearch.WordTrace tailWord_7632050 prefixEnd_7632050 3918910029146969802975847 := by
  unfold tailWord_7632050
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590933000098443803031401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185575821333595850141417069 69590933000098443803031401)
  ·
    refine ⟨52193199750073832852273551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69590933000098443803031401 52193199750073832852273551)
    ·
      refine ⟨78289799625110749278410327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52193199750073832852273551 78289799625110749278410327)
      ·
        refine ⟨117434699437666123917615491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78289799625110749278410327 117434699437666123917615491)
        ·
          refine ⟨176152049156499185876423237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117434699437666123917615491 176152049156499185876423237)
          ·
            refine ⟨33028509216843597351829357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176152049156499185876423237 33028509216843597351829357)
            ·
              refine ⟨12385690956316349006936009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33028509216843597351829357 12385690956316349006936009)
              ·
                refine ⟨9289268217237261755202007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12385690956316349006936009 9289268217237261755202007)
                ·
                  refine ⟨13933902325855892632803011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9289268217237261755202007 13933902325855892632803011)
                  ·
                    refine ⟨20900853488783838949204517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13933902325855892632803011 20900853488783838949204517)
                    ·
                      refine ⟨3918910029146969802975847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20900853488783838949204517 3918910029146969802975847)
                      ·
                        rfl

theorem cell23_7632050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_7632050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632050 prefixEnd_7632050 := by exact prefixLift 7632050
  have htrace : WordTrace (prefixWord ++ tailWord_7632050) baseStart_7632050 baseEnd_7632050 := by
    simpa [prefixWord, tailWord_7632050, baseEnd_7632050] using wordTrace_append hprefix tailTrace_7632050
  have hstable : (prefixWord ++ tailWord_7632050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632050).length < 2 ^ (prefixWord ++ tailWord_7632050).sum := by decide
  have hdescent : baseEnd_7632050 < baseStart_7632050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632078 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_7632078 : Nat := 118140960795 + 7632078 * 2 ^ 59
def prefixEnd_7632078 : Nat := 4983230072969 + 3 ^ 40 * 7632078 * 2
def baseEnd_7632078 : Nat := 3918924406605295693425719

theorem tailTrace_7632078 : CollatzResearch.WordTrace tailWord_7632078 prefixEnd_7632078 3918924406605295693425719 := by
  unfold tailWord_7632078
  simp only [CollatzResearch.WordTrace]
  refine ⟨34795594155536541999268111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185576502162861557329429925 34795594155536541999268111)
  ·
    refine ⟨52193391233304812998902167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34795594155536541999268111 52193391233304812998902167)
    ·
      refine ⟨78290086849957219498353251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52193391233304812998902167 78290086849957219498353251)
      ·
        refine ⟨117435130274935829247529877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78290086849957219498353251 117435130274935829247529877)
        ·
          refine ⟨5504771731637616995977963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117435130274935829247529877 5504771731637616995977963)
          ·
            refine ⟨8257157597456425493966945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504771731637616995977963 8257157597456425493966945)
            ·
              refine ⟨6192868198092319120475209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8257157597456425493966945 6192868198092319120475209)
              ·
                refine ⟨4644651148569239340356407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192868198092319120475209 4644651148569239340356407)
                ·
                  refine ⟨6966976722853859010534611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644651148569239340356407 6966976722853859010534611)
                  ·
                    refine ⟨10450465084280788515801917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6966976722853859010534611 10450465084280788515801917)
                    ·
                      refine ⟨3918924406605295693425719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10450465084280788515801917 3918924406605295693425719)
                      ·
                        rfl

theorem cell23_7632078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_7632078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632078 prefixEnd_7632078 := by exact prefixLift 7632078
  have htrace : WordTrace (prefixWord ++ tailWord_7632078) baseStart_7632078 baseEnd_7632078 := by
    simpa [prefixWord, tailWord_7632078, baseEnd_7632078] using wordTrace_append hprefix tailTrace_7632078
  have hstable : (prefixWord ++ tailWord_7632078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632078).length < 2 ^ (prefixWord ++ tailWord_7632078).sum := by decide
  have hdescent : baseEnd_7632078 < baseStart_7632078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632127 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 1, 3, 2]
def baseStart_7632127 : Nat := 118140960795 + 7632127 * 2 ^ 59
def prefixEnd_7632127 : Nat := 4983230072969 + 3 ^ 40 * 7632127 * 2
def baseEnd_7632127 : Nat := 3918949567157366001712993

theorem tailTrace_7632127 : CollatzResearch.WordTrace tailWord_7632127 prefixEnd_7632127 3918949567157366001712993 := by
  unfold tailWord_7632127
  simp only [CollatzResearch.WordTrace]
  refine ⟨278366540421114817362678635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185577693614076544908452423 278366540421114817362678635)
  ·
    refine ⟨417549810631672226044017953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278366540421114817362678635 417549810631672226044017953)
    ·
      refine ⟨313162357973754169533013465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417549810631672226044017953 313162357973754169533013465)
      ·
        refine ⟨234871768480315627149760099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313162357973754169533013465 234871768480315627149760099)
        ·
          refine ⟨352307652720473440724640149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234871768480315627149760099 352307652720473440724640149)
          ·
            refine ⟨16514421221272192533967507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352307652720473440724640149 16514421221272192533967507)
            ·
              refine ⟨24771631831908288800951261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16514421221272192533967507 24771631831908288800951261)
              ·
                refine ⟨9289361936965608300356723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24771631831908288800951261 9289361936965608300356723)
                ·
                  refine ⟨13934042905448412450535085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9289361936965608300356723 13934042905448412450535085)
                  ·
                    refine ⟨5225266089543154668950657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13934042905448412450535085 5225266089543154668950657)
                    ·
                      refine ⟨3918949567157366001712993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225266089543154668950657 3918949567157366001712993)
                      ·
                        rfl

theorem cell23_7632127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_7632127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632127 prefixEnd_7632127 := by exact prefixLift 7632127
  have htrace : WordTrace (prefixWord ++ tailWord_7632127) baseStart_7632127 baseEnd_7632127 := by
    simpa [prefixWord, tailWord_7632127, baseEnd_7632127] using wordTrace_append hprefix tailTrace_7632127
  have hstable : (prefixWord ++ tailWord_7632127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632127).length < 2 ^ (prefixWord ++ tailWord_7632127).sum := by decide
  have hdescent : baseEnd_7632127 < baseStart_7632127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632163 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 7]
def baseStart_7632163 : Nat := 118140960795 + 7632163 * 2 ^ 59
def prefixEnd_7632163 : Nat := 4983230072969 + 3 ^ 40 * 7632163 * 2
def baseEnd_7632163 : Nat := 435440894717880873429203

theorem tailTrace_7632163 : CollatzResearch.WordTrace tailWord_7632163 prefixEnd_7632163 435440894717880873429203 := by
  unfold tailWord_7632163
  simp only [CollatzResearch.WordTrace]
  refine ⟨278367853448984395510989143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185578568965989597007326095 278367853448984395510989143)
  ·
    refine ⟨417551780173476593266483715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278367853448984395510989143 417551780173476593266483715)
    ·
      refine ⟨626327670260214889899725573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417551780173476593266483715 626327670260214889899725573)
      ·
        refine ⟨117436438173790291856198545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 626327670260214889899725573 117436438173790291856198545)
        ·
          refine ⟨88077328630342718892148909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117436438173790291856198545 88077328630342718892148909)
          ·
            refine ⟨33028998236378519584555841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88077328630342718892148909 33028998236378519584555841)
            ·
              refine ⟨24771748677283889688416881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33028998236378519584555841 24771748677283889688416881)
              ·
                refine ⟨18578811507962917266312661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24771748677283889688416881 18578811507962917266312661)
                ·
                  refine ⟨435440894717880873429203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18578811507962917266312661 435440894717880873429203)
                  ·
                    rfl

theorem cell23_7632163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 7].length) (baseStart_7632163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632163 prefixEnd_7632163 := by exact prefixLift 7632163
  have htrace : WordTrace (prefixWord ++ tailWord_7632163) baseStart_7632163 baseEnd_7632163 := by
    simpa [prefixWord, tailWord_7632163, baseEnd_7632163] using wordTrace_append hprefix tailTrace_7632163
  have hstable : (prefixWord ++ tailWord_7632163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632163).length < 2 ^ (prefixWord ++ tailWord_7632163).sum := by decide
  have hdescent : baseEnd_7632163 < baseStart_7632163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632200 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_7632200 : Nat := 118140960795 + 7632200 * 2 ^ 59
def prefixEnd_7632200 : Nat := 4983230072969 + 3 ^ 40 * 7632200 * 2
def baseEnd_7632200 : Nat := 3918987051245144216100157

theorem tailTrace_7632200 : CollatzResearch.WordTrace tailWord_7632200 prefixEnd_7632200 3918987051245144216100157 := by
  unfold tailWord_7632200
  simp only [CollatzResearch.WordTrace]
  refine ⟨139184601474925175415043027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185579468633233567220057369 139184601474925175415043027)
  ·
    refine ⟨208776902212387763122564541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139184601474925175415043027 208776902212387763122564541)
    ·
      refine ⟨78291338329645411170961703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208776902212387763122564541 78291338329645411170961703)
      ·
        refine ⟨117437007494468116756442555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78291338329645411170961703 117437007494468116756442555)
        ·
          refine ⟨176155511241702175134663833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117437007494468116756442555 176155511241702175134663833)
          ·
            refine ⟨132116633431276631350997875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176155511241702175134663833 132116633431276631350997875)
            ·
              refine ⟨198174950146914947026496813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132116633431276631350997875 198174950146914947026496813)
              ·
                refine ⟨74315606305093105134936305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198174950146914947026496813 74315606305093105134936305)
                ·
                  refine ⟨55736704728819828851202229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74315606305093105134936305 55736704728819828851202229)
                  ·
                    refine ⟨5225316068326858954800209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55736704728819828851202229 5225316068326858954800209)
                    ·
                      refine ⟨3918987051245144216100157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225316068326858954800209 3918987051245144216100157)
                      ·
                        rfl

theorem cell23_7632200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_7632200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632200 prefixEnd_7632200 := by exact prefixLift 7632200
  have htrace : WordTrace (prefixWord ++ tailWord_7632200) baseStart_7632200 baseEnd_7632200 := by
    simpa [prefixWord, tailWord_7632200, baseEnd_7632200] using wordTrace_append hprefix tailTrace_7632200
  have hstable : (prefixWord ++ tailWord_7632200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632200).length < 2 ^ (prefixWord ++ tailWord_7632200).sum := by decide
  have hdescent : baseEnd_7632200 < baseStart_7632200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632273 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_7632273 : Nat := 118140960795 + 7632273 * 2 ^ 59
def prefixEnd_7632273 : Nat := 4983230072969 + 3 ^ 40 * 7632273 * 2
def baseEnd_7632273 : Nat := 3919024535332922430487321

theorem tailTrace_7632273 : CollatzResearch.WordTrace tailWord_7632273 prefixEnd_7632273 3919024535332922430487321 := by
  unfold tailWord_7632273
  simp only [CollatzResearch.WordTrace]
  refine ⟨278371865478585884297493473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185581243652390589531662315 278371865478585884297493473)
  ·
    refine ⟨208778899108939413223120105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278371865478585884297493473 208778899108939413223120105)
    ·
      refine ⟨156584174331704559917340079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208778899108939413223120105 156584174331704559917340079)
      ·
        refine ⟨234876261497556839876010119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156584174331704559917340079 234876261497556839876010119)
        ·
          refine ⟨352314392246335259814015179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234876261497556839876010119 352314392246335259814015179)
          ·
            refine ⟨528471588369502889721022769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352314392246335259814015179 528471588369502889721022769)
            ·
              refine ⟨396353691277127167290767077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528471588369502889721022769 396353691277127167290767077)
              ·
                refine ⟨74316317114461343867018827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396353691277127167290767077 74316317114461343867018827)
                ·
                  refine ⟨111474475671692015800528241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74316317114461343867018827 111474475671692015800528241)
                  ·
                    refine ⟨83605856753769011850396181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111474475671692015800528241 83605856753769011850396181)
                    ·
                      refine ⟨3919024535332922430487321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83605856753769011850396181 3919024535332922430487321)
                      ·
                        rfl

theorem cell23_7632273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_7632273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632273 prefixEnd_7632273 := by exact prefixLift 7632273
  have htrace : WordTrace (prefixWord ++ tailWord_7632273) baseStart_7632273 baseEnd_7632273 := by
    simpa [prefixWord, tailWord_7632273, baseEnd_7632273] using wordTrace_append hprefix tailTrace_7632273
  have hstable : (prefixWord ++ tailWord_7632273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632273).length < 2 ^ (prefixWord ++ tailWord_7632273).sum := by decide
  have hdescent : baseEnd_7632273 < baseStart_7632273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632284 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7632284 : Nat := 118140960795 + 7632284 * 2 ^ 59
def prefixEnd_7632284 : Nat := 4983230072969 + 3 ^ 40 * 7632284 * 2
def baseEnd_7632284 : Nat := 3919030183620121887449771

theorem tailTrace_7632284 : CollatzResearch.WordTrace tailWord_7632284 prefixEnd_7632284 3919030183620121887449771 := by
  unfold tailWord_7632284
  simp only [CollatzResearch.WordTrace]
  refine ⟨139186133340773016588071953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185581511121030688784095937 139186133340773016588071953)
  ·
    refine ⟨104389600005579762441053965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139186133340773016588071953 104389600005579762441053965)
    ·
      refine ⟨39146100002092410915395237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104389600005579762441053965 39146100002092410915395237)
      ·
        refine ⟨7339893750392327046636607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39146100002092410915395237 7339893750392327046636607)
        ·
          refine ⟨11009840625588490569954911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7339893750392327046636607 11009840625588490569954911)
          ·
            refine ⟨16514760938382735854932367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009840625588490569954911 16514760938382735854932367)
            ·
              refine ⟨24772141407574103782398551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16514760938382735854932367 24772141407574103782398551)
              ·
                refine ⟨37158212111361155673597827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24772141407574103782398551 37158212111361155673597827)
                ·
                  refine ⟨55737318167041733510396741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37158212111361155673597827 55737318167041733510396741)
                  ·
                    refine ⟨10450747156320325033199389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55737318167041733510396741 10450747156320325033199389)
                    ·
                      refine ⟨3919030183620121887449771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10450747156320325033199389 3919030183620121887449771)
                      ·
                        rfl

theorem cell23_7632284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7632284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632284 prefixEnd_7632284 := by exact prefixLift 7632284
  have htrace : WordTrace (prefixWord ++ tailWord_7632284) baseStart_7632284 baseEnd_7632284 := by
    simpa [prefixWord, tailWord_7632284, baseEnd_7632284] using wordTrace_append hprefix tailTrace_7632284
  have hstable : (prefixWord ++ tailWord_7632284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632284).length < 2 ^ (prefixWord ++ tailWord_7632284).sum := by decide
  have hdescent : baseEnd_7632284 < baseStart_7632284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632307 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 2, 3, 2]
def baseStart_7632307 : Nat := 118140960795 + 7632307 * 2 ^ 59
def prefixEnd_7632307 : Nat := 4983230072969 + 3 ^ 40 * 7632307 * 2
def baseEnd_7632307 : Nat := 3919041993675175297462165

theorem tailTrace_7632307 : CollatzResearch.WordTrace tailWord_7632307 prefixEnd_7632307 3919041993675175297462165 := by
  unfold tailWord_7632307
  simp only [CollatzResearch.WordTrace]
  refine ⟨278373105560462708104231175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185582070373641805402820783 278373105560462708104231175)
  ·
    refine ⟨417559658340694062156346763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278373105560462708104231175 417559658340694062156346763)
    ·
      refine ⟨626339487511041093234520145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417559658340694062156346763 626339487511041093234520145)
      ·
        refine ⟨469754615633280819925890109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626339487511041093234520145 469754615633280819925890109)
        ·
          refine ⟨176157980862480307472208791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469754615633280819925890109 176157980862480307472208791)
          ·
            refine ⟨264236971293720461208313187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176157980862480307472208791 264236971293720461208313187)
            ·
              refine ⟨396355456940580691812469781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264236971293720461208313187 396355456940580691812469781)
              ·
                refine ⟨18579162044089719928709521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396355456940580691812469781 18579162044089719928709521)
                ·
                  refine ⟨13934371533067289946532141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18579162044089719928709521 13934371533067289946532141)
                  ·
                    refine ⟨5225389324900233729949553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13934371533067289946532141 5225389324900233729949553)
                    ·
                      refine ⟨3919041993675175297462165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225389324900233729949553 3919041993675175297462165)
                      ·
                        rfl

theorem cell23_7632307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3, 2].length) (baseStart_7632307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632307 prefixEnd_7632307 := by exact prefixLift 7632307
  have htrace : WordTrace (prefixWord ++ tailWord_7632307) baseStart_7632307 baseEnd_7632307 := by
    simpa [prefixWord, tailWord_7632307, baseEnd_7632307] using wordTrace_append hprefix tailTrace_7632307
  have hstable : (prefixWord ++ tailWord_7632307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632307).length < 2 ^ (prefixWord ++ tailWord_7632307).sum := by decide
  have hdescent : baseEnd_7632307 < baseStart_7632307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632320 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_7632320 : Nat := 118140960795 + 7632320 * 2 ^ 59
def prefixEnd_7632320 : Nat := 4983230072969 + 3 ^ 40 * 7632320 * 2
def baseEnd_7632320 : Nat := 3919048668923683746599605

theorem tailTrace_7632320 : CollatzResearch.WordTrace tailWord_7632320 prefixEnd_7632320 3919048668923683746599605 := by
  unfold tailWord_7632320
  simp only [CollatzResearch.WordTrace]
  refine ⟨139186789854707805662227207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185582386472943740882969609 139186789854707805662227207)
  ·
    refine ⟨208780184782061708493340811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139186789854707805662227207 208780184782061708493340811)
    ·
      refine ⟨313170277173092562740011217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208780184782061708493340811 313170277173092562740011217)
      ·
        refine ⟨234877707879819422055008413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313170277173092562740011217 234877707879819422055008413)
        ·
          refine ⟨88079140454932283270628155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234877707879819422055008413 88079140454932283270628155)
          ·
            refine ⟨132118710682398424905942233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88079140454932283270628155 132118710682398424905942233)
            ·
              refine ⟨99089033011798818679456675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132118710682398424905942233 99089033011798818679456675)
              ·
                refine ⟨148633549517698228019185013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99089033011798818679456675 148633549517698228019185013)
                ·
                  refine ⟨13934395267284208876798595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148633549517698228019185013 13934395267284208876798595)
                  ·
                    refine ⟨20901592900926313315197893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13934395267284208876798595 20901592900926313315197893)
                    ·
                      refine ⟨3919048668923683746599605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20901592900926313315197893 3919048668923683746599605)
                      ·
                        rfl

theorem cell23_7632320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_7632320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632320 prefixEnd_7632320 := by exact prefixLift 7632320
  have htrace : WordTrace (prefixWord ++ tailWord_7632320) baseStart_7632320 baseEnd_7632320 := by
    simpa [prefixWord, tailWord_7632320, baseEnd_7632320] using wordTrace_append hprefix tailTrace_7632320
  have hstable : (prefixWord ++ tailWord_7632320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632320).length < 2 ^ (prefixWord ++ tailWord_7632320).sum := by decide
  have hdescent : baseEnd_7632320 < baseStart_7632320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632324 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7632324 : Nat := 118140960795 + 7632324 * 2 ^ 59
def prefixEnd_7632324 : Nat := 4983230072969 + 3 ^ 40 * 7632324 * 2
def baseEnd_7632324 : Nat := 3919050722846301730949587

theorem tailTrace_7632324 : CollatzResearch.WordTrace tailWord_7632324 prefixEnd_7632324 3919050722846301730949587 := by
  unfold tailWord_7632324
  simp only [CollatzResearch.WordTrace]
  refine ⟨139186862800700560003800013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185582483734267413338400017 139186862800700560003800013)
  ·
    refine ⟨52195073550262710001425005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139186862800700560003800013 52195073550262710001425005)
    ·
      refine ⟨19573152581348516250534377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52195073550262710001425005 19573152581348516250534377)
      ·
        refine ⟨14679864436011387187900783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19573152581348516250534377 14679864436011387187900783)
        ·
          refine ⟨22019796654017080781851175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679864436011387187900783 22019796654017080781851175)
          ·
            refine ⟨33029694981025621172776763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22019796654017080781851175 33029694981025621172776763)
            ·
              refine ⟨49544542471538431759165145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33029694981025621172776763 49544542471538431759165145)
              ·
                refine ⟨37158406853653823819373859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49544542471538431759165145 37158406853653823819373859)
                ·
                  refine ⟨55737610280480735729060789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37158406853653823819373859 55737610280480735729060789)
                  ·
                    refine ⟨5225400963795068974599449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55737610280480735729060789 5225400963795068974599449)
                    ·
                      refine ⟨3919050722846301730949587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225400963795068974599449 3919050722846301730949587)
                      ·
                        rfl

theorem cell23_7632324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7632324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632324 prefixEnd_7632324 := by exact prefixLift 7632324
  have htrace : WordTrace (prefixWord ++ tailWord_7632324) baseStart_7632324 baseEnd_7632324 := by
    simpa [prefixWord, tailWord_7632324, baseEnd_7632324] using wordTrace_append hprefix tailTrace_7632324
  have hstable : (prefixWord ++ tailWord_7632324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632324).length < 2 ^ (prefixWord ++ tailWord_7632324).sum := by decide
  have hdescent : baseEnd_7632324 < baseStart_7632324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632357 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7632357 : Nat := 118140960795 + 7632357 * 2 ^ 59
def prefixEnd_7632357 : Nat := 4983230072969 + 3 ^ 40 * 7632357 * 2
def baseEnd_7632357 : Nat := 3919067667707900101836935

theorem tailTrace_7632357 : CollatzResearch.WordTrace tailWord_7632357 prefixEnd_7632357 3919067667707900101836935 := by
  unfold tailWord_7632357
  simp only [CollatzResearch.WordTrace]
  refine ⟨278374929210281566643551325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185583286140187711095700883 278374929210281566643551325)
  ·
    refine ⟨104390598453855587491331747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278374929210281566643551325 104390598453855587491331747)
    ·
      refine ⟨156585897680783381236997621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104390598453855587491331747 156585897680783381236997621)
      ·
        refine ⟨14679927907573441990968527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156585897680783381236997621 14679927907573441990968527)
        ·
          refine ⟨22019891861360162986452791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679927907573441990968527 22019891861360162986452791)
          ·
            refine ⟨33029837792040244479679187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22019891861360162986452791 33029837792040244479679187)
            ·
              refine ⟨49544756688060366719518781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33029837792040244479679187 49544756688060366719518781)
              ·
                refine ⟨18579283758022637519819543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49544756688060366719518781 18579283758022637519819543)
                ·
                  refine ⟨27868925637033956279729315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18579283758022637519819543 27868925637033956279729315)
                  ·
                    refine ⟨41803388455550934419593973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27868925637033956279729315 41803388455550934419593973)
                    ·
                      refine ⟨3919067667707900101836935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41803388455550934419593973 3919067667707900101836935)
                      ·
                        rfl

theorem cell23_7632357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7632357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632357 prefixEnd_7632357 := by exact prefixLift 7632357
  have htrace : WordTrace (prefixWord ++ tailWord_7632357) baseStart_7632357 baseEnd_7632357 := by
    simpa [prefixWord, tailWord_7632357, baseEnd_7632357] using wordTrace_append hprefix tailTrace_7632357
  have hstable : (prefixWord ++ tailWord_7632357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632357).length < 2 ^ (prefixWord ++ tailWord_7632357).sum := by decide
  have hdescent : baseEnd_7632357 < baseStart_7632357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632365 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_7632365 : Nat := 118140960795 + 7632365 * 2 ^ 59
def prefixEnd_7632365 : Nat := 4983230072969 + 3 ^ 40 * 7632365 * 2
def baseEnd_7632365 : Nat := 3919071775553136070536899

theorem tailTrace_7632365 : CollatzResearch.WordTrace tailWord_7632365 prefixEnd_7632365 3919071775553136070536899 := by
  unfold tailWord_7632365
  simp only [CollatzResearch.WordTrace]
  refine ⟨278375220994252584009842549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185583480662835056006561699 278375220994252584009842549)
  ·
    refine ⟨26097676968211179750922739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278375220994252584009842549 26097676968211179750922739)
    ·
      refine ⟨39146515452316769626384109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26097676968211179750922739 39146515452316769626384109)
      ·
        refine ⟨14679943294618788609894041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39146515452316769626384109 14679943294618788609894041)
        ·
          refine ⟨11009957470964091457420531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14679943294618788609894041 11009957470964091457420531)
          ·
            refine ⟨16514936206446137186130797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009957470964091457420531 16514936206446137186130797)
            ·
              refine ⟨6193101077417301444799049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16514936206446137186130797 6193101077417301444799049)
              ·
                refine ⟨4644825808062976083599287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6193101077417301444799049 4644825808062976083599287)
                ·
                  refine ⟨6967238712094464125398931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644825808062976083599287 6967238712094464125398931)
                  ·
                    refine ⟨10450858068141696188098397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6967238712094464125398931 10450858068141696188098397)
                    ·
                      refine ⟨3919071775553136070536899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10450858068141696188098397 3919071775553136070536899)
                      ·
                        rfl

theorem cell23_7632365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_7632365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632365 prefixEnd_7632365 := by exact prefixLift 7632365
  have htrace : WordTrace (prefixWord ++ tailWord_7632365) baseStart_7632365 baseEnd_7632365 := by
    simpa [prefixWord, tailWord_7632365, baseEnd_7632365] using wordTrace_append hprefix tailTrace_7632365
  have hstable : (prefixWord ++ tailWord_7632365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632365).length < 2 ^ (prefixWord ++ tailWord_7632365).sum := by decide
  have hdescent : baseEnd_7632365 < baseStart_7632365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632381 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_7632381 : Nat := 118140960795 + 7632381 * 2 ^ 59
def prefixEnd_7632381 : Nat := 4983230072969 + 3 ^ 40 * 7632381 * 2
def baseEnd_7632381 : Nat := 1306359997081202669312275

theorem tailTrace_7632381 : CollatzResearch.WordTrace tailWord_7632381 prefixEnd_7632381 1306359997081202669312275 := by
  unfold tailWord_7632381
  simp only [CollatzResearch.WordTrace]
  refine ⟨278375804562194618742424997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185583869708129745828283331 278375804562194618742424997)
  ·
    refine ⟨52195463355411491014204687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278375804562194618742424997 52195463355411491014204687)
    ·
      refine ⟨78293195033117236521307031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52195463355411491014204687 78293195033117236521307031)
      ·
        refine ⟨117439792549675854781960547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78293195033117236521307031 117439792549675854781960547)
        ·
          refine ⟨176159688824513782172940821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117439792549675854781960547 176159688824513782172940821)
          ·
            refine ⟨8257485413649083539356601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176159688824513782172940821 8257485413649083539356601)
            ·
              refine ⟨6193114060236812654517451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8257485413649083539356601 6193114060236812654517451)
              ·
                refine ⟨9289671090355218981776177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193114060236812654517451 9289671090355218981776177)
                ·
                  refine ⟨6967253317766414236332133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9289671090355218981776177 6967253317766414236332133)
                  ·
                    refine ⟨1306359997081202669312275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967253317766414236332133 1306359997081202669312275)
                    ·
                      rfl

theorem cell23_7632381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_7632381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632381 prefixEnd_7632381 := by exact prefixLift 7632381
  have htrace : WordTrace (prefixWord ++ tailWord_7632381) baseStart_7632381 baseEnd_7632381 := by
    simpa [prefixWord, tailWord_7632381, baseEnd_7632381] using wordTrace_append hprefix tailTrace_7632381
  have hstable : (prefixWord ++ tailWord_7632381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632381).length < 2 ^ (prefixWord ++ tailWord_7632381).sum := by decide
  have hdescent : baseEnd_7632381 < baseStart_7632381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632387 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 3]
def baseStart_7632387 : Nat := 118140960795 + 7632387 * 2 ^ 59
def prefixEnd_7632387 : Nat := 4983230072969 + 3 ^ 40 * 7632387 * 2
def baseEnd_7632387 : Nat := 3919083072127534984461797

theorem tailTrace_7632387 : CollatzResearch.WordTrace tailWord_7632387 prefixEnd_7632387 3919083072127534984461797 := by
  unfold tailWord_7632387
  simp only [CollatzResearch.WordTrace]
  refine ⟨278376023400172881767143415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185584015600115254511428943 278376023400172881767143415)
  ·
    refine ⟨417564035100259322650715123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278376023400172881767143415 417564035100259322650715123)
    ·
      refine ⟨626346052650388983976072685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417564035100259322650715123 626346052650388983976072685)
      ·
        refine ⟨234879769743895868991027257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626346052650388983976072685 234879769743895868991027257)
        ·
          refine ⟨176159827307921901743270443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234879769743895868991027257 176159827307921901743270443)
          ·
            refine ⟨264239740961882852614905665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176159827307921901743270443 264239740961882852614905665)
            ·
              refine ⟨198179805721412139461179249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264239740961882852614905665 198179805721412139461179249)
              ·
                refine ⟨148634854291059104595884437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198179805721412139461179249 148634854291059104595884437)
                ·
                  refine ⟨6967258794893395527932083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148634854291059104595884437 6967258794893395527932083)
                  ·
                    refine ⟨10450888192340093291898125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6967258794893395527932083 10450888192340093291898125)
                    ·
                      refine ⟨3919083072127534984461797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10450888192340093291898125 3919083072127534984461797)
                      ·
                        rfl

theorem cell23_7632387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_7632387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632387 prefixEnd_7632387 := by exact prefixLift 7632387
  have htrace : WordTrace (prefixWord ++ tailWord_7632387) baseStart_7632387 baseEnd_7632387 := by
    simpa [prefixWord, tailWord_7632387, baseEnd_7632387] using wordTrace_append hprefix tailTrace_7632387
  have hstable : (prefixWord ++ tailWord_7632387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632387).length < 2 ^ (prefixWord ++ tailWord_7632387).sum := by decide
  have hdescent : baseEnd_7632387 < baseStart_7632387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632388 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_7632388 : Nat := 118140960795 + 7632388 * 2 ^ 59
def prefixEnd_7632388 : Nat := 4983230072969 + 3 ^ 40 * 7632388 * 2
def baseEnd_7632388 : Nat := 3919083585608189480549293

theorem tailTrace_7632388 : CollatzResearch.WordTrace tailWord_7632388 prefixEnd_7632388 3919083585608189480549293 := by
  unfold tailWord_7632388
  simp only [CollatzResearch.WordTrace]
  refine ⟨139188029936584629468964909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185584039915446172625286545 139188029936584629468964909)
  ·
    refine ⟨52195511226219236050861841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139188029936584629468964909 52195511226219236050861841)
    ·
      refine ⟨39146633419664427038146381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52195511226219236050861841 39146633419664427038146381)
      ·
        refine ⟨14679987532374160139304893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39146633419664427038146381 14679987532374160139304893)
        ·
          refine ⟨5504995324640310052239335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14679987532374160139304893 5504995324640310052239335)
          ·
            refine ⟨8257492986960465078359003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504995324640310052239335 8257492986960465078359003)
            ·
              refine ⟨12386239480440697617538505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257492986960465078359003 12386239480440697617538505)
              ·
                refine ⟨9289679610330523213153879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386239480440697617538505 9289679610330523213153879)
                ·
                  refine ⟨13934519415495784819730819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9289679610330523213153879 13934519415495784819730819)
                  ·
                    refine ⟨20901779123243677229596229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13934519415495784819730819 20901779123243677229596229)
                    ·
                      refine ⟨3919083585608189480549293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20901779123243677229596229 3919083585608189480549293)
                      ·
                        rfl

theorem cell23_7632388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_7632388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632388 prefixEnd_7632388 := by exact prefixLift 7632388
  have htrace : WordTrace (prefixWord ++ tailWord_7632388) baseStart_7632388 baseEnd_7632388 := by
    simpa [prefixWord, tailWord_7632388, baseEnd_7632388] using wordTrace_append hprefix tailTrace_7632388
  have hstable : (prefixWord ++ tailWord_7632388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632388).length < 2 ^ (prefixWord ++ tailWord_7632388).sum := by decide
  have hdescent : baseEnd_7632388 < baseStart_7632388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632391 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_7632391 : Nat := 118140960795 + 7632391 * 2 ^ 59
def prefixEnd_7632391 : Nat := 4983230072969 + 3 ^ 40 * 7632391 * 2
def baseEnd_7632391 : Nat := 3919085126050152968811779

theorem tailTrace_7632391 : CollatzResearch.WordTrace tailWord_7632391 prefixEnd_7632391 3919085126050152968811779 := by
  unfold tailWord_7632391
  simp only [CollatzResearch.WordTrace]
  refine ⟨278376169292158390450289027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185584112861438926966859351 278376169292158390450289027)
  ·
    refine ⟨417564253938237585675433541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278376169292158390450289027 417564253938237585675433541)
    ·
      refine ⟨78293297613419547314143789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417564253938237585675433541 78293297613419547314143789)
      ·
        refine ⟨29359986605032330242803921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78293297613419547314143789 29359986605032330242803921)
        ·
          refine ⟨22019989953774247682102941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29359986605032330242803921 22019989953774247682102941)
          ·
            refine ⟨8257496232665342880788603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22019989953774247682102941 8257496232665342880788603)
            ·
              refine ⟨12386244348998014321182905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257496232665342880788603 12386244348998014321182905)
              ·
                refine ⟨9289683261748510740887179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386244348998014321182905 9289683261748510740887179)
                ·
                  refine ⟨13934524892622766111330769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9289683261748510740887179 13934524892622766111330769)
                  ·
                    refine ⟨10450893669467074583498077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13934524892622766111330769 10450893669467074583498077)
                    ·
                      refine ⟨3919085126050152968811779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10450893669467074583498077 3919085126050152968811779)
                      ·
                        rfl

theorem cell23_7632391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_7632391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632391 prefixEnd_7632391 := by exact prefixLift 7632391
  have htrace : WordTrace (prefixWord ++ tailWord_7632391) baseStart_7632391 baseEnd_7632391 := by
    simpa [prefixWord, tailWord_7632391, baseEnd_7632391] using wordTrace_append hprefix tailTrace_7632391
  have hstable : (prefixWord ++ tailWord_7632391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632391).length < 2 ^ (prefixWord ++ tailWord_7632391).sum := by decide
  have hdescent : baseEnd_7632391 < baseStart_7632391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632437 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7632437 : Nat := 118140960795 + 7632437 * 2 ^ 59
def prefixEnd_7632437 : Nat := 4983230072969 + 3 ^ 40 * 7632437 * 2
def baseEnd_7632437 : Nat := 1306369582053419929612189

theorem tailTrace_7632437 : CollatzResearch.WordTrace tailWord_7632437 prefixEnd_7632437 1306369582053419929612189 := by
  unfold tailWord_7632437
  simp only [CollatzResearch.WordTrace]
  refine ⟨278377847049991740306463565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185585231366661160204309043 278377847049991740306463565)
  ·
    refine ⟨104391692643746902614923837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278377847049991740306463565 104391692643746902614923837)
    ·
      refine ⟨39146884741405088480596439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104391692643746902614923837 39146884741405088480596439)
      ·
        refine ⟨58720327112107632720894659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39146884741405088480596439 58720327112107632720894659)
        ·
          refine ⟨88080490668161449081341989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58720327112107632720894659 88080490668161449081341989)
          ·
            refine ⟨16515092000280271702751623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88080490668161449081341989 16515092000280271702751623)
            ·
              refine ⟨24772638000420407554127435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16515092000280271702751623 24772638000420407554127435)
              ·
                refine ⟨37158957000630611331191153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24772638000420407554127435 37158957000630611331191153)
                ·
                  refine ⟨27869217750472958498393365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37158957000630611331191153 27869217750472958498393365)
                  ·
                    refine ⟨1306369582053419929612189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27869217750472958498393365 1306369582053419929612189)
                    ·
                      rfl

theorem cell23_7632437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7632437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632437 prefixEnd_7632437 := by exact prefixLift 7632437
  have htrace : WordTrace (prefixWord ++ tailWord_7632437) baseStart_7632437 baseEnd_7632437 := by
    simpa [prefixWord, tailWord_7632437, baseEnd_7632437] using wordTrace_append hprefix tailTrace_7632437
  have hstable : (prefixWord ++ tailWord_7632437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632437).length < 2 ^ (prefixWord ++ tailWord_7632437).sum := by decide
  have hdescent : baseEnd_7632437 < baseStart_7632437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632484 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 5]
def baseStart_7632484 : Nat := 118140960795 + 7632484 * 2 ^ 59
def prefixEnd_7632484 : Nat := 4983230072969 + 3 ^ 40 * 7632484 * 2
def baseEnd_7632484 : Nat := 435459208861224567216539

theorem tailTrace_7632484 : CollatzResearch.WordTrace tailWord_7632484 prefixEnd_7632484 435459208861224567216539 := by
  unfold tailWord_7632484
  simp only [CollatzResearch.WordTrace]
  refine ⟨139189780640410733666712253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185586374187214311555616337 139189780640410733666712253)
  ·
    refine ⟨52196167740154025125017095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139189780640410733666712253 52196167740154025125017095)
    ·
      refine ⟨78294251610231037687525643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52196167740154025125017095 78294251610231037687525643)
      ·
        refine ⟨117441377415346556531288465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78294251610231037687525643 117441377415346556531288465)
        ·
          refine ⟨88081033061509917398466349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117441377415346556531288465 88081033061509917398466349)
          ·
            refine ⟨33030387398066219024424881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88081033061509917398466349 33030387398066219024424881)
            ·
              refine ⟨24772790548549664268318661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33030387398066219024424881 24772790548549664268318661)
              ·
                refine ⟨4644898227853062050309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24772790548549664268318661 4644898227853062050309749)
                ·
                  refine ⟨435459208861224567216539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4644898227853062050309749 435459208861224567216539)
                  ·
                    rfl

theorem cell23_7632484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_7632484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632484 prefixEnd_7632484 := by exact prefixLift 7632484
  have htrace : WordTrace (prefixWord ++ tailWord_7632484) baseStart_7632484 baseEnd_7632484 := by
    simpa [prefixWord, tailWord_7632484, baseEnd_7632484] using wordTrace_append hprefix tailTrace_7632484
  have hstable : (prefixWord ++ tailWord_7632484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632484).length < 2 ^ (prefixWord ++ tailWord_7632484).sum := by decide
  have hdescent : baseEnd_7632484 < baseStart_7632484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632517 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_7632517 : Nat := 118140960795 + 7632517 * 2 ^ 59
def prefixEnd_7632517 : Nat := 4983230072969 + 3 ^ 40 * 7632517 * 2
def baseEnd_7632517 : Nat := 3919149824612619475836199

theorem tailTrace_7632517 : CollatzResearch.WordTrace tailWord_7632517 prefixEnd_7632517 3919149824612619475836199 := by
  unfold tailWord_7632517
  simp only [CollatzResearch.WordTrace]
  refine ⟨278380764889701913969375805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185587176593134609312917203 278380764889701913969375805)
  ·
    refine ⟨104392786833638217738515927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278380764889701913969375805 104392786833638217738515927)
    ·
      refine ⟨156589180250457326607773891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104392786833638217738515927 156589180250457326607773891)
      ·
        refine ⟨234883770375685989911660837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156589180250457326607773891 234883770375685989911660837)
        ·
          refine ⟨44040706945441123108436407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234883770375685989911660837 44040706945441123108436407)
          ·
            refine ⟨66061060418161684662654611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44040706945441123108436407 66061060418161684662654611)
            ·
              refine ⟨99091590627242526993981917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66061060418161684662654611 99091590627242526993981917)
              ·
                refine ⟨37159346485215947622743219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99091590627242526993981917 37159346485215947622743219)
                ·
                  refine ⟨55739019727823921434114829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37159346485215947622743219 55739019727823921434114829)
                  ·
                    refine ⟨20902132397933970537793061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55739019727823921434114829 20902132397933970537793061)
                    ·
                      refine ⟨3919149824612619475836199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20902132397933970537793061 3919149824612619475836199)
                      ·
                        rfl

theorem cell23_7632517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_7632517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632517 prefixEnd_7632517 := by exact prefixLift 7632517
  have htrace : WordTrace (prefixWord ++ tailWord_7632517) baseStart_7632517 baseEnd_7632517 := by
    simpa [prefixWord, tailWord_7632517, baseEnd_7632517] using wordTrace_append hprefix tailTrace_7632517
  have hstable : (prefixWord ++ tailWord_7632517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632517).length < 2 ^ (prefixWord ++ tailWord_7632517).sum := by decide
  have hdescent : baseEnd_7632517 < baseStart_7632517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632537 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_7632537 : Nat := 118140960795 + 7632537 * 2 ^ 59
def prefixEnd_7632537 : Nat := 4983230072969 + 3 ^ 40 * 7632537 * 2
def baseEnd_7632537 : Nat := 3919160094225709397586107

theorem tailTrace_7632537 : CollatzResearch.WordTrace tailWord_7632537 prefixEnd_7632537 3919160094225709397586107 := by
  unfold tailWord_7632537
  simp only [CollatzResearch.WordTrace]
  refine ⟨278381494349629457385103865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185587662899752971590069243 278381494349629457385103865)
  ·
    refine ⟨208786120762222093038827899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278381494349629457385103865 208786120762222093038827899)
    ·
      refine ⟨313179181143333139558241849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208786120762222093038827899 313179181143333139558241849)
      ·
        refine ⟨234884385857499854668681387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313179181143333139558241849 234884385857499854668681387)
        ·
          refine ⟨352326578786249782003022081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234884385857499854668681387 352326578786249782003022081)
          ·
            refine ⟨264244934089687336502266561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352326578786249782003022081 264244934089687336502266561)
            ·
              refine ⟨198183700567265502376699921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264244934089687336502266561 198183700567265502376699921)
              ·
                refine ⟨148637775425449126782524941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198183700567265502376699921 148637775425449126782524941)
                ·
                  refine ⟨55739165784543422543446853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148637775425449126782524941 55739165784543422543446853)
                  ·
                    refine ⟨10451093584601891726896285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55739165784543422543446853 10451093584601891726896285)
                    ·
                      refine ⟨3919160094225709397586107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10451093584601891726896285 3919160094225709397586107)
                      ·
                        rfl

theorem cell23_7632537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_7632537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632537 prefixEnd_7632537 := by exact prefixLift 7632537
  have htrace : WordTrace (prefixWord ++ tailWord_7632537) baseStart_7632537 baseEnd_7632537 := by
    simpa [prefixWord, tailWord_7632537, baseEnd_7632537] using wordTrace_append hprefix tailTrace_7632537
  have hstable : (prefixWord ++ tailWord_7632537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632537).length < 2 ^ (prefixWord ++ tailWord_7632537).sum := by decide
  have hdescent : baseEnd_7632537 < baseStart_7632537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632624 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2]
def baseStart_7632624 : Nat := 118140960795 + 7632624 * 2 ^ 59
def prefixEnd_7632624 : Nat := 4983230072969 + 3 ^ 40 * 7632624 * 2
def baseEnd_7632624 : Nat := 3919204767042650557198207

theorem tailTrace_7632624 : CollatzResearch.WordTrace tailWord_7632624 prefixEnd_7632624 3919204767042650557198207 := by
  unfold tailWord_7632624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139192333750157135621760463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185589778333542847495680617 139192333750157135621760463)
  ·
    refine ⟨208788500625235703432640695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139192333750157135621760463 208788500625235703432640695)
    ·
      refine ⟨313182750937853555148961043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208788500625235703432640695 313182750937853555148961043)
      ·
        refine ⟨469774126406780332723441565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313182750937853555148961043 469774126406780332723441565)
        ·
          refine ⟨176165297402542624771290587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469774126406780332723441565 176165297402542624771290587)
          ·
            refine ⟨264247946103813937156935881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176165297402542624771290587 264247946103813937156935881)
            ·
              refine ⟨198185959577860452867701911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264247946103813937156935881 198185959577860452867701911)
              ·
                refine ⟨297278939366790679301552867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198185959577860452867701911 297278939366790679301552867)
                ·
                  refine ⟨445918409050186018952329301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297278939366790679301552867 445918409050186018952329301)
                  ·
                    refine ⟨5225606356056867409597609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 445918409050186018952329301 5225606356056867409597609)
                    ·
                      refine ⟨3919204767042650557198207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225606356056867409597609 3919204767042650557198207)
                      ·
                        rfl

theorem cell23_7632624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 8, 2].length) (baseStart_7632624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632624 prefixEnd_7632624 := by exact prefixLift 7632624
  have htrace : WordTrace (prefixWord ++ tailWord_7632624) baseStart_7632624 baseEnd_7632624 := by
    simpa [prefixWord, tailWord_7632624, baseEnd_7632624] using wordTrace_append hprefix tailTrace_7632624
  have hstable : (prefixWord ++ tailWord_7632624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632624).length < 2 ^ (prefixWord ++ tailWord_7632624).sum := by decide
  have hdescent : baseEnd_7632624 < baseStart_7632624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632634 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_7632634 : Nat := 118140960795 + 7632634 * 2 ^ 59
def prefixEnd_7632634 : Nat := 4983230072969 + 3 ^ 40 * 7632634 * 2
def baseEnd_7632634 : Nat := 1306403300616398506024387

theorem tailTrace_7632634 : CollatzResearch.WordTrace tailWord_7632634 prefixEnd_7632634 1306403300616398506024387 := by
  unfold tailWord_7632634
  simp only [CollatzResearch.WordTrace]
  refine ⟨69596258057569510737846239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185590021486852028634256637 69596258057569510737846239)
  ·
    refine ⟨104394387086354266106769359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69596258057569510737846239 104394387086354266106769359)
    ·
      refine ⟨156591580629531399160154039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104394387086354266106769359 156591580629531399160154039)
      ·
        refine ⟨234887370944297098740231059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156591580629531399160154039 234887370944297098740231059)
        ·
          refine ⟨352331056416445648110346589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234887370944297098740231059 352331056416445648110346589)
          ·
            refine ⟨132124146156167118041379971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352331056416445648110346589 132124146156167118041379971)
            ·
              refine ⟨198186219234250677062069957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132124146156167118041379971 198186219234250677062069957)
              ·
                refine ⟨37159916106422001949138117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198186219234250677062069957 37159916106422001949138117)
                ·
                  refine ⟨6967484269954125365463397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37159916106422001949138117 6967484269954125365463397)
                  ·
                    refine ⟨1306403300616398506024387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967484269954125365463397 1306403300616398506024387)
                    ·
                      rfl

theorem cell23_7632634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_7632634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632634 prefixEnd_7632634 := by exact prefixLift 7632634
  have htrace : WordTrace (prefixWord ++ tailWord_7632634) baseStart_7632634 baseEnd_7632634 := by
    simpa [prefixWord, tailWord_7632634, baseEnd_7632634] using wordTrace_append hprefix tailTrace_7632634
  have hstable : (prefixWord ++ tailWord_7632634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632634).length < 2 ^ (prefixWord ++ tailWord_7632634).sum := by decide
  have hdescent : baseEnd_7632634 < baseStart_7632634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632638 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7632638 : Nat := 118140960795 + 7632638 * 2 ^ 59
def prefixEnd_7632638 : Nat := 4983230072969 + 3 ^ 40 * 7632638 * 2
def baseEnd_7632638 : Nat := 1306403985257271167474381

theorem tailTrace_7632638 : CollatzResearch.WordTrace tailWord_7632638 prefixEnd_7632638 1306403985257271167474381 := by
  unfold tailWord_7632638
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798147265282943954316321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185590118748175701089687045 34798147265282943954316321)
  ·
    refine ⟨26098610448962207965737241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34798147265282943954316321 26098610448962207965737241)
    ·
      refine ⟨19573957836721655974302931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26098610448962207965737241 19573957836721655974302931)
      ·
        refine ⟨29360936755082483961454397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19573957836721655974302931 29360936755082483961454397)
        ·
          refine ⟨11010351283155931485545399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29360936755082483961454397 11010351283155931485545399)
          ·
            refine ⟨16515526924733897228318099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010351283155931485545399 16515526924733897228318099)
            ·
              refine ⟨24773290387100845842477149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16515526924733897228318099 24773290387100845842477149)
              ·
                refine ⟨9289983895162817190928931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24773290387100845842477149 9289983895162817190928931)
                ·
                  refine ⟨13934975842744225786393397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9289983895162817190928931 13934975842744225786393397)
                  ·
                    refine ⟨1306403985257271167474381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13934975842744225786393397 1306403985257271167474381)
                    ·
                      rfl

theorem cell23_7632638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7632638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632638 prefixEnd_7632638 := by exact prefixLift 7632638
  have htrace : WordTrace (prefixWord ++ tailWord_7632638) baseStart_7632638 baseEnd_7632638 := by
    simpa [prefixWord, tailWord_7632638, baseEnd_7632638] using wordTrace_append hprefix tailTrace_7632638
  have hstable : (prefixWord ++ tailWord_7632638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632638).length < 2 ^ (prefixWord ++ tailWord_7632638).sum := by decide
  have hdescent : baseEnd_7632638 < baseStart_7632638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632651 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 2, 4]
def baseStart_7632651 : Nat := 118140960795 + 7632651 * 2 ^ 59
def prefixEnd_7632651 : Nat := 4983230072969 + 3 ^ 40 * 7632651 * 2
def baseEnd_7632651 : Nat := 1306406210340107317186861

theorem tailTrace_7632651 : CollatzResearch.WordTrace tailWord_7632651 prefixEnd_7632651 1306406210340107317186861 := by
  unfold tailWord_7632651
  simp only [CollatzResearch.WordTrace]
  refine ⟨278385652271216454854753807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185590434847477636569835871 278385652271216454854753807)
  ·
    refine ⟨417578478406824682282130711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278385652271216454854753807 417578478406824682282130711)
    ·
      refine ⟨626367717610237023423196067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417578478406824682282130711 626367717610237023423196067)
      ·
        refine ⟨939551576415355535134794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626367717610237023423196067 939551576415355535134794101)
        ·
          refine ⟨88082960288939581418886947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 939551576415355535134794101 88082960288939581418886947)
          ·
            refine ⟨132124440433409372128330421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88082960288939581418886947 132124440433409372128330421)
            ·
              refine ⟨12386666290632128637030977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132124440433409372128330421 12386666290632128637030977)
              ·
                refine ⟨9289999717974096477773233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386666290632128637030977 9289999717974096477773233)
                ·
                  refine ⟨6967499788480572358329925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9289999717974096477773233 6967499788480572358329925)
                  ·
                    refine ⟨1306406210340107317186861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967499788480572358329925 1306406210340107317186861)
                    ·
                      rfl

theorem cell23_7632651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 4].length) (baseStart_7632651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632651 prefixEnd_7632651 := by exact prefixLift 7632651
  have htrace : WordTrace (prefixWord ++ tailWord_7632651) baseStart_7632651 baseEnd_7632651 := by
    simpa [prefixWord, tailWord_7632651, baseEnd_7632651] using wordTrace_append hprefix tailTrace_7632651
  have hstable : (prefixWord ++ tailWord_7632651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632651).length < 2 ^ (prefixWord ++ tailWord_7632651).sum := by decide
  have hdescent : baseEnd_7632651 < baseStart_7632651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632654 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7632654 : Nat := 118140960795 + 7632654 * 2 ^ 59
def prefixEnd_7632654 : Nat := 4983230072969 + 3 ^ 40 * 7632654 * 2
def baseEnd_7632654 : Nat := 3919220171462285439823069

theorem tailTrace_7632654 : CollatzResearch.WordTrace tailWord_7632654 prefixEnd_7632654 3919220171462285439823069 := by
  unfold tailWord_7632654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798220211275698295889127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185590507793470390911408677 34798220211275698295889127)
  ·
    refine ⟨52197330316913547443833691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34798220211275698295889127 52197330316913547443833691)
    ·
      refine ⟨78295995475370321165750537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52197330316913547443833691 78295995475370321165750537)
      ·
        refine ⟨58721996606527740874312903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78295995475370321165750537 58721996606527740874312903)
        ·
          refine ⟨88082994909791611311469355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58721996606527740874312903 88082994909791611311469355)
          ·
            refine ⟨132124492364687416967204033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88082994909791611311469355 132124492364687416967204033)
            ·
              refine ⟨99093369273515562725403025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132124492364687416967204033 99093369273515562725403025)
              ·
                refine ⟨74320026955136672044052269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99093369273515562725403025 74320026955136672044052269)
                ·
                  refine ⟨27870010108176252016519601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74320026955136672044052269 27870010108176252016519601)
                  ·
                    refine ⟨20902507581132189012389701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27870010108176252016519601 20902507581132189012389701)
                    ·
                      refine ⟨3919220171462285439823069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20902507581132189012389701 3919220171462285439823069)
                      ·
                        rfl

theorem cell23_7632654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7632654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632654 prefixEnd_7632654 := by exact prefixLift 7632654
  have htrace : WordTrace (prefixWord ++ tailWord_7632654) baseStart_7632654 baseEnd_7632654 := by
    simpa [prefixWord, tailWord_7632654, baseEnd_7632654] using wordTrace_append hprefix tailTrace_7632654
  have hstable : (prefixWord ++ tailWord_7632654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632654).length < 2 ^ (prefixWord ++ tailWord_7632654).sum := by decide
  have hdescent : baseEnd_7632654 < baseStart_7632654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632657 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_7632657 : Nat := 118140960795 + 7632657 * 2 ^ 59
def prefixEnd_7632657 : Nat := 4983230072969 + 3 ^ 40 * 7632657 * 2
def baseEnd_7632657 : Nat := 3919221711904248928085555

theorem tailTrace_7632657 : CollatzResearch.WordTrace tailWord_7632657 prefixEnd_7632657 3919221711904248928085555 := by
  unfold tailWord_7632657
  simp only [CollatzResearch.WordTrace]
  refine ⟨278385871109194717879472225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185590580739463145252981483 278385871109194717879472225)
  ·
    refine ⟨208789403331896038409604169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278385871109194717879472225 208789403331896038409604169)
    ·
      refine ⟨156592052498922028807203127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208789403331896038409604169 156592052498922028807203127)
      ·
        refine ⟨234888078748383043210804691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156592052498922028807203127 234888078748383043210804691)
        ·
          refine ⟨352332118122574564816207037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234888078748383043210804691 352332118122574564816207037)
          ·
            refine ⟨132124544295965461806077639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352332118122574564816207037 132124544295965461806077639)
            ·
              refine ⟨198186816443948192709116459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132124544295965461806077639 198186816443948192709116459)
              ·
                refine ⟨297280224665922289063674689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198186816443948192709116459 297280224665922289063674689)
                ·
                  refine ⟨222960168499441716797756017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297280224665922289063674689 222960168499441716797756017)
                  ·
                    refine ⟨167220126374581287598317013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222960168499441716797756017 167220126374581287598317013)
                    ·
                      refine ⟨3919221711904248928085555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167220126374581287598317013 3919221711904248928085555)
                      ·
                        rfl

theorem cell23_7632657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_7632657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632657 prefixEnd_7632657 := by exact prefixLift 7632657
  have htrace : WordTrace (prefixWord ++ tailWord_7632657) baseStart_7632657 baseEnd_7632657 := by
    simpa [prefixWord, tailWord_7632657, baseEnd_7632657] using wordTrace_append hprefix tailTrace_7632657
  have hstable : (prefixWord ++ tailWord_7632657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632657).length < 2 ^ (prefixWord ++ tailWord_7632657).sum := by decide
  have hdescent : baseEnd_7632657 < baseStart_7632657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632667 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_7632667 : Nat := 118140960795 + 7632667 * 2 ^ 59
def prefixEnd_7632667 : Nat := 4983230072969 + 3 ^ 40 * 7632667 * 2
def baseEnd_7632667 : Nat := 3919226846710793888960509

theorem tailTrace_7632667 : CollatzResearch.WordTrace tailWord_7632667 prefixEnd_7632667 3919226846710793888960509 := by
  unfold tailWord_7632667
  simp only [CollatzResearch.WordTrace]
  refine ⟨278386235839158489587336255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185590823892772326391557503 278386235839158489587336255)
  ·
    refine ⟨417579353758737734381004383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278386235839158489587336255 417579353758737734381004383)
    ·
      refine ⟨626369030638106601571506575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417579353758737734381004383 626369030638106601571506575)
      ·
        refine ⟨939553545957159902357259863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626369030638106601571506575 939553545957159902357259863)
        ·
          refine ⟨1409330318935739853535889795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939553545957159902357259863 1409330318935739853535889795)
          ·
            refine ⟨2113995478403609780303834693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409330318935739853535889795 2113995478403609780303834693)
            ·
              refine ⟨396374152200676833806969005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2113995478403609780303834693 396374152200676833806969005)
              ·
                refine ⟨148640307075253812677613377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396374152200676833806969005 148640307075253812677613377)
                ·
                  refine ⟨111480230306440359508210033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148640307075253812677613377 111480230306440359508210033)
                  ·
                    refine ⟨83610172729830269631157525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111480230306440359508210033 83610172729830269631157525)
                    ·
                      refine ⟨3919226846710793888960509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83610172729830269631157525 3919226846710793888960509)
                      ·
                        rfl

theorem cell23_7632667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_7632667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632667 prefixEnd_7632667 := by exact prefixLift 7632667
  have htrace : WordTrace (prefixWord ++ tailWord_7632667) baseStart_7632667 baseEnd_7632667 := by
    simpa [prefixWord, tailWord_7632667, baseEnd_7632667] using wordTrace_append hprefix tailTrace_7632667
  have hstable : (prefixWord ++ tailWord_7632667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632667).length < 2 ^ (prefixWord ++ tailWord_7632667).sum := by decide
  have hdescent : baseEnd_7632667 < baseStart_7632667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632668 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_7632668 : Nat := 118140960795 + 7632668 * 2 ^ 59
def prefixEnd_7632668 : Nat := 4983230072969 + 3 ^ 40 * 7632668 * 2
def baseEnd_7632668 : Nat := 1306409120063816128349335

theorem tailTrace_7632668 : CollatzResearch.WordTrace tailWord_7632668 prefixEnd_7632668 1306409120063816128349335 := by
  unfold tailWord_7632668
  simp only [CollatzResearch.WordTrace]
  refine ⟨139193136156077433379061329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185590848208103244505415105 139193136156077433379061329)
  ·
    refine ⟨104394852117058075034295997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139193136156077433379061329 104394852117058075034295997)
    ·
      refine ⟨39148069543896778137860999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104394852117058075034295997 39148069543896778137860999)
      ·
        refine ⟨58722104315845167206791499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39148069543896778137860999 58722104315845167206791499)
        ·
          refine ⟨88083156473767750810187249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58722104315845167206791499 88083156473767750810187249)
          ·
            refine ⟨66062367355325813107640437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88083156473767750810187249 66062367355325813107640437)
            ·
              refine ⟨6193346939561794978841291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66062367355325813107640437 6193346939561794978841291)
              ·
                refine ⟨9290020409342692468261937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193346939561794978841291 9290020409342692468261937)
                ·
                  refine ⟨6967515307007019351196453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290020409342692468261937 6967515307007019351196453)
                  ·
                    refine ⟨1306409120063816128349335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967515307007019351196453 1306409120063816128349335)
                    ·
                      rfl

theorem cell23_7632668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_7632668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632668 prefixEnd_7632668 := by exact prefixLift 7632668
  have htrace : WordTrace (prefixWord ++ tailWord_7632668) baseStart_7632668 baseEnd_7632668 := by
    simpa [prefixWord, tailWord_7632668, baseEnd_7632668] using wordTrace_append hprefix tailTrace_7632668
  have hstable : (prefixWord ++ tailWord_7632668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632668).length < 2 ^ (prefixWord ++ tailWord_7632668).sum := by decide
  have hdescent : baseEnd_7632668 < baseStart_7632668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632714 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_7632714 : Nat := 118140960795 + 7632714 * 2 ^ 59
def prefixEnd_7632714 : Nat := 4983230072969 + 3 ^ 40 * 7632714 * 2
def baseEnd_7632714 : Nat := 3919250980301555205072793

theorem tailTrace_7632714 : CollatzResearch.WordTrace tailWord_7632714 prefixEnd_7632714 3919250980301555205072793 := by
  unfold tailWord_7632714
  simp only [CollatzResearch.WordTrace]
  refine ⟨69596987517497054153574299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185591966713325477742864797 69596987517497054153574299)
  ·
    refine ⟨104395481276245581230361449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69596987517497054153574299 104395481276245581230361449)
    ·
      refine ⟨78296610957184185922771087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104395481276245581230361449 78296610957184185922771087)
      ·
        refine ⟨117444916435776278884156631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78296610957184185922771087 117444916435776278884156631)
        ·
          refine ⟨176167374653664418326234947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117444916435776278884156631 176167374653664418326234947)
          ·
            refine ⟨264251061980496627489352421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176167374653664418326234947 264251061980496627489352421)
            ·
              refine ⟨49547074121343117654253579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264251061980496627489352421 49547074121343117654253579)
              ·
                refine ⟨74320611182014676481380369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49547074121343117654253579 74320611182014676481380369)
                ·
                  refine ⟨55740458386511007361035277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74320611182014676481380369 55740458386511007361035277)
                  ·
                    refine ⟨20902671894941627760388229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55740458386511007361035277 20902671894941627760388229)
                    ·
                      refine ⟨3919250980301555205072793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20902671894941627760388229 3919250980301555205072793)
                      ·
                        rfl

theorem cell23_7632714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_7632714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632714 prefixEnd_7632714 := by exact prefixLift 7632714
  have htrace : WordTrace (prefixWord ++ tailWord_7632714) baseStart_7632714 baseEnd_7632714 := by
    simpa [prefixWord, tailWord_7632714, baseEnd_7632714] using wordTrace_append hprefix tailTrace_7632714
  have hstable : (prefixWord ++ tailWord_7632714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632714).length < 2 ^ (prefixWord ++ tailWord_7632714).sum := by decide
  have hdescent : baseEnd_7632714 < baseStart_7632714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632725 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_7632725 : Nat := 118140960795 + 7632725 * 2 ^ 59
def prefixEnd_7632725 : Nat := 4983230072969 + 3 ^ 40 * 7632725 * 2
def baseEnd_7632725 : Nat := 3919256628588754662035243

theorem tailTrace_7632725 : CollatzResearch.WordTrace tailWord_7632725 prefixEnd_7632725 3919256628588754662035243 := by
  unfold tailWord_7632725
  simp only [CollatzResearch.WordTrace]
  refine ⟨278388351272948365492947629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185592234181965576995298419 278388351272948365492947629)
  ·
    refine ⟨104395631727355637059855361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278388351272948365492947629 104395631727355637059855361)
    ·
      refine ⟨78296723795516727794891521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104395631727355637059855361 78296723795516727794891521)
      ·
        refine ⟨58722542846637545846168641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78296723795516727794891521 58722542846637545846168641)
        ·
          refine ⟨44041907134978159384626481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58722542846637545846168641 44041907134978159384626481)
          ·
            refine ⟨33031430351233619538469861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44041907134978159384626481 33031430351233619538469861)
            ·
              refine ⟨6193393190856303663463099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33031430351233619538469861 6193393190856303663463099)
              ·
                refine ⟨9290089786284455495194649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193393190856303663463099 9290089786284455495194649)
                ·
                  refine ⟨6967567339713341621395987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290089786284455495194649 6967567339713341621395987)
                  ·
                    refine ⟨10451351009570012432093981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6967567339713341621395987 10451351009570012432093981)
                    ·
                      refine ⟨3919256628588754662035243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10451351009570012432093981 3919256628588754662035243)
                      ·
                        rfl

theorem cell23_7632725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_7632725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632725 prefixEnd_7632725 := by exact prefixLift 7632725
  have htrace : WordTrace (prefixWord ++ tailWord_7632725) baseStart_7632725 baseEnd_7632725 := by
    simpa [prefixWord, tailWord_7632725, baseEnd_7632725] using wordTrace_append hprefix tailTrace_7632725
  have hstable : (prefixWord ++ tailWord_7632725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632725).length < 2 ^ (prefixWord ++ tailWord_7632725).sum := by decide
  have hdescent : baseEnd_7632725 < baseStart_7632725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632735 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 1, 3, 2]
def baseStart_7632735 : Nat := 118140960795 + 7632735 * 2 ^ 59
def prefixEnd_7632735 : Nat := 4983230072969 + 3 ^ 40 * 7632735 * 2
def baseEnd_7632735 : Nat := 3919261763395299622910197

theorem tailTrace_7632735 : CollatzResearch.WordTrace tailWord_7632735 prefixEnd_7632735 3919261763395299622910197 := by
  unfold tailWord_7632735
  simp only [CollatzResearch.WordTrace]
  refine ⟨278388716002912137200811659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185592477335274758133874439 278388716002912137200811659)
  ·
    refine ⟨417583074004368205801217489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278388716002912137200811659 417583074004368205801217489)
    ·
      refine ⟨313187305503276154350913117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417583074004368205801217489 313187305503276154350913117)
      ·
        refine ⟨117445239563728557881592419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313187305503276154350913117 117445239563728557881592419)
        ·
          refine ⟨176167859345592836822388629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117445239563728557881592419 176167859345592836822388629)
          ·
            refine ⟨8257868406824664226049467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176167859345592836822388629 8257868406824664226049467)
            ·
              refine ⟨12386802610236996339074201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257868406824664226049467 12386802610236996339074201)
              ·
                refine ⟨9290101957677747254305651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386802610236996339074201 9290101957677747254305651)
                ·
                  refine ⟨13935152936516620881458477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9290101957677747254305651 13935152936516620881458477)
                  ·
                    refine ⟨5225682351193732830546929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13935152936516620881458477 5225682351193732830546929)
                    ·
                      refine ⟨3919261763395299622910197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225682351193732830546929 3919261763395299622910197)
                      ·
                        rfl

theorem cell23_7632735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_7632735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632735 prefixEnd_7632735 := by exact prefixLift 7632735
  have htrace : WordTrace (prefixWord ++ tailWord_7632735) baseStart_7632735 baseEnd_7632735 := by
    simpa [prefixWord, tailWord_7632735, baseEnd_7632735] using wordTrace_append hprefix tailTrace_7632735
  have hstable : (prefixWord ++ tailWord_7632735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632735).length < 2 ^ (prefixWord ++ tailWord_7632735).sum := by decide
  have hdescent : baseEnd_7632735 < baseStart_7632735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632748 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_7632748 : Nat := 118140960795 + 7632748 * 2 ^ 59
def prefixEnd_7632748 : Nat := 4983230072969 + 3 ^ 40 * 7632748 * 2
def baseEnd_7632748 : Nat := 3919268438643808072047637

theorem tailTrace_7632748 : CollatzResearch.WordTrace tailWord_7632748 prefixEnd_7632748 3919268438643808072047637 := by
  unfold tailWord_7632748
  simp only [CollatzResearch.WordTrace]
  refine ⟨139194595075932520210517449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185592793434576693614023265 139194595075932520210517449)
  ·
    refine ⟨104395946306949390157888087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139194595075932520210517449 104395946306949390157888087)
    ·
      refine ⟨156593919460424085236832131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104395946306949390157888087 156593919460424085236832131)
      ·
        refine ⟨234890879190636127855248197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156593919460424085236832131 234890879190636127855248197)
        ·
          refine ⟨44042039848244273972859037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234890879190636127855248197 44042039848244273972859037)
          ·
            refine ⟨16515764943091602739822139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44042039848244273972859037 16515764943091602739822139)
            ·
              refine ⟨24773647414637404109733209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16515764943091602739822139 24773647414637404109733209)
              ·
                refine ⟨18580235560978053082299907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24773647414637404109733209 18580235560978053082299907)
                ·
                  refine ⟨27870353341467079623449861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18580235560978053082299907 27870353341467079623449861)
                  ·
                    refine ⟨5225691251525077429396849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27870353341467079623449861 5225691251525077429396849)
                    ·
                      refine ⟨3919268438643808072047637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225691251525077429396849 3919268438643808072047637)
                      ·
                        rfl

theorem cell23_7632748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_7632748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632748 prefixEnd_7632748 := by exact prefixLift 7632748
  have htrace : WordTrace (prefixWord ++ tailWord_7632748) baseStart_7632748 baseEnd_7632748 := by
    simpa [prefixWord, tailWord_7632748, baseEnd_7632748] using wordTrace_append hprefix tailTrace_7632748
  have hstable : (prefixWord ++ tailWord_7632748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632748).length < 2 ^ (prefixWord ++ tailWord_7632748).sum := by decide
  have hdescent : baseEnd_7632748 < baseStart_7632748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632778 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7632778 : Nat := 118140960795 + 7632778 * 2 ^ 59
def prefixEnd_7632778 : Nat := 4983230072969 + 3 ^ 40 * 7632778 * 2
def baseEnd_7632778 : Nat := 3919283843063442954672499

theorem tailTrace_7632778 : CollatzResearch.WordTrace tailWord_7632778 prefixEnd_7632778 3919283843063442954672499 := by
  unfold tailWord_7632778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69597571085439088886156747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185593522894504237029751325 69597571085439088886156747)
  ·
    refine ⟨104396356628158633329235121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69597571085439088886156747 104396356628158633329235121)
    ·
      refine ⟨78297267471118974996926341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104396356628158633329235121 78297267471118974996926341)
      ·
        refine ⟨14680737650834807811923689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78297267471118974996926341 14680737650834807811923689)
        ·
          refine ⟨11010553238126105858942767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14680737650834807811923689 11010553238126105858942767)
          ·
            refine ⟨16515829857189158788414151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010553238126105858942767 16515829857189158788414151)
            ·
              refine ⟨24773744785783738182621227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16515829857189158788414151 24773744785783738182621227)
              ·
                refine ⟨37160617178675607273931841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24773744785783738182621227 37160617178675607273931841)
                ·
                  refine ⟨27870462884006705455448881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37160617178675607273931841 27870462884006705455448881)
                  ·
                    refine ⟨20902847163005029091586661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27870462884006705455448881 20902847163005029091586661)
                    ·
                      refine ⟨3919283843063442954672499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20902847163005029091586661 3919283843063442954672499)
                      ·
                        rfl

theorem cell23_7632778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7632778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632778 prefixEnd_7632778 := by exact prefixLift 7632778
  have htrace : WordTrace (prefixWord ++ tailWord_7632778) baseStart_7632778 baseEnd_7632778 := by
    simpa [prefixWord, tailWord_7632778, baseEnd_7632778] using wordTrace_append hprefix tailTrace_7632778
  have hstable : (prefixWord ++ tailWord_7632778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632778).length < 2 ^ (prefixWord ++ tailWord_7632778).sum := by decide
  have hdescent : baseEnd_7632778 < baseStart_7632778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632782 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7632782 : Nat := 118140960795 + 7632782 * 2 ^ 59
def prefixEnd_7632782 : Nat := 4983230072969 + 3 ^ 40 * 7632782 * 2
def baseEnd_7632782 : Nat := 3919285896986060939022481

theorem tailTrace_7632782 : CollatzResearch.WordTrace tailWord_7632782 prefixEnd_7632782 3919285896986060939022481 := by
  unfold tailWord_7632782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798803779217733028471575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185593620155827909485181733 34798803779217733028471575)
  ·
    refine ⟨52198205668826599542707363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34798803779217733028471575 52198205668826599542707363)
    ·
      refine ⟨78297308503239899314061045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52198205668826599542707363 78297308503239899314061045)
      ·
        refine ⟨7340372672178740560693223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78297308503239899314061045 7340372672178740560693223)
        ·
          refine ⟨11010559008268110841039835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340372672178740560693223 11010559008268110841039835)
          ·
            refine ⟨16515838512402166261559753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010559008268110841039835 16515838512402166261559753)
            ·
              refine ⟨12386878884301624696169815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16515838512402166261559753 12386878884301624696169815)
              ·
                refine ⟨18580318326452437044254723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386878884301624696169815 18580318326452437044254723)
                ·
                  refine ⟨27870477489678655566382085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18580318326452437044254723 27870477489678655566382085)
                  ·
                    refine ⟨5225714529314747918696641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27870477489678655566382085 5225714529314747918696641)
                    ·
                      refine ⟨3919285896986060939022481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225714529314747918696641 3919285896986060939022481)
                      ·
                        rfl

theorem cell23_7632782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7632782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632782 prefixEnd_7632782 := by exact prefixLift 7632782
  have htrace : WordTrace (prefixWord ++ tailWord_7632782) baseStart_7632782 baseEnd_7632782 := by
    simpa [prefixWord, tailWord_7632782, baseEnd_7632782] using wordTrace_append hprefix tailTrace_7632782
  have hstable : (prefixWord ++ tailWord_7632782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632782).length < 2 ^ (prefixWord ++ tailWord_7632782).sum := by decide
  have hdescent : baseEnd_7632782 < baseStart_7632782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632784 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_7632784 : Nat := 118140960795 + 7632784 * 2 ^ 59
def prefixEnd_7632784 : Nat := 4983230072969 + 3 ^ 40 * 7632784 * 2
def baseEnd_7632784 : Nat := 1306428974649123310399157

theorem tailTrace_7632784 : CollatzResearch.WordTrace tailWord_7632784 prefixEnd_7632784 1306428974649123310399157 := by
  unfold tailWord_7632784
  simp only [CollatzResearch.WordTrace]
  refine ⟨139195251589867309284672703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185593668786489745712896937 139195251589867309284672703)
  ·
    refine ⟨208792877384800963927009055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139195251589867309284672703 208792877384800963927009055)
    ·
      refine ⟨313189316077201445890513583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208792877384800963927009055 313189316077201445890513583)
      ·
        refine ⟨469783974115802168835770375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313189316077201445890513583 469783974115802168835770375)
        ·
          refine ⟨704675961173703253253655563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469783974115802168835770375 704675961173703253253655563)
          ·
            refine ⟨1057013941760554879880483345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704675961173703253253655563 1057013941760554879880483345)
            ·
              refine ⟨792760456320416159910362509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057013941760554879880483345 792760456320416159910362509)
              ·
                refine ⟨297285171120156059966385941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 792760456320416159910362509 297285171120156059966385941)
                ·
                  refine ⟨13935242396257315310924341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 297285171120156059966385941 13935242396257315310924341)
                  ·
                    refine ⟨1306428974649123310399157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13935242396257315310924341 1306428974649123310399157)
                    ·
                      rfl

theorem cell23_7632784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_7632784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632784 prefixEnd_7632784 := by exact prefixLift 7632784
  have htrace : WordTrace (prefixWord ++ tailWord_7632784) baseStart_7632784 baseEnd_7632784 := by
    simpa [prefixWord, tailWord_7632784, baseEnd_7632784] using wordTrace_append hprefix tailTrace_7632784
  have hstable : (prefixWord ++ tailWord_7632784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632784).length < 2 ^ (prefixWord ++ tailWord_7632784).sum := by decide
  have hdescent : baseEnd_7632784 < baseStart_7632784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632841 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_7632841 : Nat := 118140960795 + 7632841 * 2 ^ 59
def prefixEnd_7632841 : Nat := 4983230072969 + 3 ^ 40 * 7632841 * 2
def baseEnd_7632841 : Nat := 3919316192344676208184709

theorem tailTrace_7632841 : CollatzResearch.WordTrace tailWord_7632841 prefixEnd_7632841 3919316192344676208184709 := by
  unfold tailWord_7632841
  simp only [CollatzResearch.WordTrace]
  refine ⟨278392582140528117304170377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185595054760352078202780251 278392582140528117304170377)
  ·
    refine ⟨208794436605396087978127783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278392582140528117304170377 208794436605396087978127783)
    ·
      refine ⟨313191654908094131967191675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208794436605396087978127783 313191654908094131967191675)
      ·
        refine ⟨469787482362141197950787513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313191654908094131967191675 469787482362141197950787513)
        ·
          refine ⟨352340611771605898463090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469787482362141197950787513 352340611771605898463090635)
          ·
            refine ⟨528510917657408847694635953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352340611771605898463090635 528510917657408847694635953)
            ·
              refine ⟨396383188243056635770976965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528510917657408847694635953 396383188243056635770976965)
              ·
                refine ⟨74321847795573119207058181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396383188243056635770976965 74321847795573119207058181)
                ·
                  refine ⟨13935346461669959851323409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74321847795573119207058181 13935346461669959851323409)
                  ·
                    refine ⟨10451509846252469888492557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13935346461669959851323409 10451509846252469888492557)
                    ·
                      refine ⟨3919316192344676208184709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10451509846252469888492557 3919316192344676208184709)
                      ·
                        rfl

theorem cell23_7632841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_7632841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632841 prefixEnd_7632841 := by exact prefixLift 7632841
  have htrace : WordTrace (prefixWord ++ tailWord_7632841) baseStart_7632841 baseEnd_7632841 := by
    simpa [prefixWord, tailWord_7632841, baseEnd_7632841] using wordTrace_append hprefix tailTrace_7632841
  have hstable : (prefixWord ++ tailWord_7632841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632841).length < 2 ^ (prefixWord ++ tailWord_7632841).sum := by decide
  have hdescent : baseEnd_7632841 < baseStart_7632841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632865 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 1, 4]
def baseStart_7632865 : Nat := 118140960795 + 7632865 * 2 ^ 59
def prefixEnd_7632865 : Nat := 4983230072969 + 3 ^ 40 * 7632865 * 2
def baseEnd_7632865 : Nat := 1306442838626794704761533

theorem tailTrace_7632865 : CollatzResearch.WordTrace tailWord_7632865 prefixEnd_7632865 1306442838626794704761533 := by
  unfold tailWord_7632865
  simp only [CollatzResearch.WordTrace]
  refine ⟨278393457492441169403044049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185595638328294112935362699 278393457492441169403044049)
  ·
    refine ⟨208795093119330877052283037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278393457492441169403044049 208795093119330877052283037)
    ·
      refine ⟨78298159919749078894606139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208795093119330877052283037 78298159919749078894606139)
      ·
        refine ⟨117447239879623618341909209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78298159919749078894606139 117447239879623618341909209)
        ·
          refine ⟨88085429909717713756431907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117447239879623618341909209 88085429909717713756431907)
          ·
            refine ⟨132128144864576570634647861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88085429909717713756431907 132128144864576570634647861)
            ·
              refine ⟨12387013581054053496998237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132128144864576570634647861 12387013581054053496998237)
              ·
                refine ⟨4645130092895270061374339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12387013581054053496998237 4645130092895270061374339)
                ·
                  refine ⟨6967695139342905092061509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645130092895270061374339 6967695139342905092061509)
                  ·
                    refine ⟨1306442838626794704761533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967695139342905092061509 1306442838626794704761533)
                    ·
                      rfl

theorem cell23_7632865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_7632865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632865 prefixEnd_7632865 := by exact prefixLift 7632865
  have htrace : WordTrace (prefixWord ++ tailWord_7632865) baseStart_7632865 baseEnd_7632865 := by
    simpa [prefixWord, tailWord_7632865, baseEnd_7632865] using wordTrace_append hprefix tailTrace_7632865
  have hstable : (prefixWord ++ tailWord_7632865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632865).length < 2 ^ (prefixWord ++ tailWord_7632865).sum := by decide
  have hdescent : baseEnd_7632865 < baseStart_7632865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632951 : List Nat := [1, 1, 3, 1, 2, 2, 5, 8]
def baseStart_7632951 : Nat := 118140960795 + 7632951 * 2 ^ 59
def prefixEnd_7632951 : Nat := 4983230072969 + 3 ^ 40 * 7632951 * 2
def baseEnd_7632951 : Nat := 145161950933950769548489

theorem tailTrace_7632951 : CollatzResearch.WordTrace tailWord_7632951 prefixEnd_7632951 145161950933950769548489 := by
  unfold tailWord_7632951
  simp only [CollatzResearch.WordTrace]
  refine ⟨278396594170129606090674707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185597729446753070727116471 278396594170129606090674707)
  ·
    refine ⟨417594891255194409136012061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278396594170129606090674707 417594891255194409136012061)
    ·
      refine ⟨156598084220697903426004523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417594891255194409136012061 156598084220697903426004523)
      ·
        refine ⟨234897126331046855139006785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156598084220697903426004523 234897126331046855139006785)
        ·
          refine ⟨176172844748285141354255089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234897126331046855139006785 176172844748285141354255089)
          ·
            refine ⟨132129633561213856015691317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176172844748285141354255089 132129633561213856015691317)
            ·
              refine ⟨12387153146363799001471061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132129633561213856015691317 12387153146363799001471061)
              ·
                refine ⟨145161950933950769548489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12387153146363799001471061 145161950933950769548489)
                ·
                  rfl

theorem cell23_7632951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 8].length) (baseStart_7632951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632951 prefixEnd_7632951 := by exact prefixLift 7632951
  have htrace : WordTrace (prefixWord ++ tailWord_7632951) baseStart_7632951 baseEnd_7632951 := by
    simpa [prefixWord, tailWord_7632951, baseEnd_7632951] using wordTrace_append hprefix tailTrace_7632951
  have hstable : (prefixWord ++ tailWord_7632951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632951).length < 2 ^ (prefixWord ++ tailWord_7632951).sum := by decide
  have hdescent : baseEnd_7632951 < baseStart_7632951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632989 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7632989 : Nat := 118140960795 + 7632989 * 2 ^ 59
def prefixEnd_7632989 : Nat := 4983230072969 + 3 ^ 40 * 7632989 * 2
def baseEnd_7632989 : Nat := 1306464062493847209711343

theorem tailTrace_7632989 : CollatzResearch.WordTrace tailWord_7632989 prefixEnd_7632989 1306464062493847209711343 := by
  unfold tailWord_7632989
  simp only [CollatzResearch.WordTrace]
  refine ⟨278397980143991938580558021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185598653429327959053705347 278397980143991938580558021)
  ·
    refine ⟨52199621276998488483854629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278397980143991938580558021 52199621276998488483854629)
    ·
      refine ⟨9787428989437216590722743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52199621276998488483854629 9787428989437216590722743)
      ·
        refine ⟨14681143484155824886084115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9787428989437216590722743 14681143484155824886084115)
        ·
          refine ⟨22021715226233737329126173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14681143484155824886084115 22021715226233737329126173)
          ·
            refine ⟨8258143209837651498422315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22021715226233737329126173 8258143209837651498422315)
            ·
              refine ⟨12387214814756477247633473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258143209837651498422315 12387214814756477247633473)
              ·
                refine ⟨9290411111067357935725105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12387214814756477247633473 9290411111067357935725105)
                ·
                  refine ⟨6967808333300518451793829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290411111067357935725105 6967808333300518451793829)
                  ·
                    refine ⟨1306464062493847209711343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967808333300518451793829 1306464062493847209711343)
                    ·
                      rfl

theorem cell23_7632989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7632989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632989 prefixEnd_7632989 := by exact prefixLift 7632989
  have htrace : WordTrace (prefixWord ++ tailWord_7632989) baseStart_7632989 baseEnd_7632989 := by
    simpa [prefixWord, tailWord_7632989, baseEnd_7632989] using wordTrace_append hprefix tailTrace_7632989
  have hstable : (prefixWord ++ tailWord_7632989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632989).length < 2 ^ (prefixWord ++ tailWord_7632989).sum := by decide
  have hdescent : baseEnd_7632989 < baseStart_7632989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7632991 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_7632991 : Nat := 118140960795 + 7632991 * 2 ^ 59
def prefixEnd_7632991 : Nat := 4983230072969 + 3 ^ 40 * 7632991 * 2
def baseEnd_7632991 : Nat := 3919393214442850621309019

theorem tailTrace_7632991 : CollatzResearch.WordTrace tailWord_7632991 prefixEnd_7632991 3919393214442850621309019 := by
  unfold tailWord_7632991
  simp only [CollatzResearch.WordTrace]
  refine ⟨278398053089984692922130827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185598702059989795281420551 278398053089984692922130827)
  ·
    refine ⟨417597079634977039383196241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278398053089984692922130827 417597079634977039383196241)
    ·
      refine ⟨313197809726232779537397181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417597079634977039383196241 313197809726232779537397181)
      ·
        refine ⟨117449178647337292326523943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313197809726232779537397181 117449178647337292326523943)
        ·
          refine ⟨176173767971005938489785915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117449178647337292326523943 176173767971005938489785915)
          ·
            refine ⟨264260651956508907734678873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176173767971005938489785915 264260651956508907734678873)
            ·
              refine ⟨198195488967381680801009155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264260651956508907734678873 198195488967381680801009155)
              ·
                refine ⟨297293233451072521201513733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198195488967381680801009155 297293233451072521201513733)
                ·
                  refine ⟨55742481272076097725283825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297293233451072521201513733 55742481272076097725283825)
                  ·
                    refine ⟨41806860954057073293962869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55742481272076097725283825 41806860954057073293962869)
                    ·
                      refine ⟨3919393214442850621309019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41806860954057073293962869 3919393214442850621309019)
                      ·
                        rfl

theorem cell23_7632991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_7632991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7632991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7632991 prefixEnd_7632991 := by exact prefixLift 7632991
  have htrace : WordTrace (prefixWord ++ tailWord_7632991) baseStart_7632991 baseEnd_7632991 := by
    simpa [prefixWord, tailWord_7632991, baseEnd_7632991] using wordTrace_append hprefix tailTrace_7632991
  have hstable : (prefixWord ++ tailWord_7632991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7632991).length < 2 ^ (prefixWord ++ tailWord_7632991).sum := by decide
  have hdescent : baseEnd_7632991 < baseStart_7632991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7632991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633051 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_7633051 : Nat := 118140960795 + 7633051 * 2 ^ 59
def prefixEnd_7633051 : Nat := 4983230072969 + 3 ^ 40 * 7633051 * 2
def baseEnd_7633051 : Nat := 3919424023282120386558743

theorem tailTrace_7633051 : CollatzResearch.WordTrace tailWord_7633051 prefixEnd_7633051 3919424023282120386558743 := by
  unfold tailWord_7633051
  simp only [CollatzResearch.WordTrace]
  refine ⟨278400241469767323169315007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185600160979844882112876671 278400241469767323169315007)
  ·
    refine ⟨417600362204650984753972511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278400241469767323169315007 417600362204650984753972511)
    ·
      refine ⟨626400543306976477130958767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417600362204650984753972511 626400543306976477130958767)
      ·
        refine ⟨939600814960464715696438151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626400543306976477130958767 939600814960464715696438151)
        ·
          refine ⟨1409401222440697073544657227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939600814960464715696438151 1409401222440697073544657227)
          ·
            refine ⟨2114101833661045610316985841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409401222440697073544657227 2114101833661045610316985841)
            ·
              refine ⟨1585576375245784207737739381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114101833661045610316985841 1585576375245784207737739381)
              ·
                refine ⟨148647785179292269475413067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1585576375245784207737739381 148647785179292269475413067)
                ·
                  refine ⟨222971677768938404213119601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148647785179292269475413067 222971677768938404213119601)
                  ·
                    refine ⟨167228758326703803159839701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 222971677768938404213119601 167228758326703803159839701)
                    ·
                      refine ⟨3919424023282120386558743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167228758326703803159839701 3919424023282120386558743)
                      ·
                        rfl

theorem cell23_7633051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_7633051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633051 prefixEnd_7633051 := by exact prefixLift 7633051
  have htrace : WordTrace (prefixWord ++ tailWord_7633051) baseStart_7633051 baseEnd_7633051 := by
    simpa [prefixWord, tailWord_7633051, baseEnd_7633051] using wordTrace_append hprefix tailTrace_7633051
  have hstable : (prefixWord ++ tailWord_7633051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633051).length < 2 ^ (prefixWord ++ tailWord_7633051).sum := by decide
  have hdescent : baseEnd_7633051 < baseStart_7633051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633052 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7633052 : Nat := 118140960795 + 7633052 * 2 ^ 59
def prefixEnd_7633052 : Nat := 4983230072969 + 3 ^ 40 * 7633052 * 2
def baseEnd_7633052 : Nat := 3919424536762774882646239

theorem tailTrace_7633052 : CollatzResearch.WordTrace tailWord_7633052 prefixEnd_7633052 3919424536762774882646239 := by
  unfold tailWord_7633052
  simp only [CollatzResearch.WordTrace]
  refine ⟨139200138971381850170050705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185600185295175800226734273 139200138971381850170050705)
  ·
    refine ⟨104400104228536387627538029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139200138971381850170050705 104400104228536387627538029)
    ·
      refine ⟨39150039085701145360326761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104400104228536387627538029 39150039085701145360326761)
      ·
        refine ⟨29362529314275859020245071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39150039085701145360326761 29362529314275859020245071)
        ·
          refine ⟨44043793971413788530367607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29362529314275859020245071 44043793971413788530367607)
          ·
            refine ⟨66065690957120682795551411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44043793971413788530367607 66065690957120682795551411)
            ·
              refine ⟨99098536435681024193327117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66065690957120682795551411 99098536435681024193327117)
              ·
                refine ⟨37161951163380384072497669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99098536435681024193327117 37161951163380384072497669)
                ·
                  refine ⟨6967865843133822013593313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37161951163380384072497669 6967865843133822013593313)
                  ·
                    refine ⟨5225899382350366510194985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6967865843133822013593313 5225899382350366510194985)
                    ·
                      refine ⟨3919424536762774882646239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5225899382350366510194985 3919424536762774882646239)
                      ·
                        rfl

theorem cell23_7633052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7633052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633052 prefixEnd_7633052 := by exact prefixLift 7633052
  have htrace : WordTrace (prefixWord ++ tailWord_7633052) baseStart_7633052 baseEnd_7633052 := by
    simpa [prefixWord, tailWord_7633052, baseEnd_7633052] using wordTrace_append hprefix tailTrace_7633052
  have hstable : (prefixWord ++ tailWord_7633052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633052).length < 2 ^ (prefixWord ++ tailWord_7633052).sum := by decide
  have hdescent : baseEnd_7633052 < baseStart_7633052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633063 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7633063 : Nat := 118140960795 + 7633063 * 2 ^ 59
def prefixEnd_7633063 : Nat := 4983230072969 + 3 ^ 40 * 7633063 * 2
def baseEnd_7633063 : Nat := 3919430185049974339608689

theorem tailTrace_7633063 : CollatzResearch.WordTrace tailWord_7633063 prefixEnd_7633063 3919430185049974339608689 := by
  unfold tailWord_7633063
  simp only [CollatzResearch.WordTrace]
  refine ⟨278400679145723849218751843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185600452763815899479167895 278400679145723849218751843)
  ·
    refine ⟨417601018718585773828127765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278400679145723849218751843 417601018718585773828127765)
    ·
      refine ⟨19575047752433708148193489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 417601018718585773828127765 19575047752433708148193489)
      ·
        refine ⟨14681285814325281111145117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19575047752433708148193489 14681285814325281111145117)
        ·
          refine ⟨5505482180371980416679419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14681285814325281111145117 5505482180371980416679419)
          ·
            refine ⟨8258223270557970625019129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505482180371980416679419 8258223270557970625019129)
            ·
              refine ⟨6193667452918477968764347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8258223270557970625019129 6193667452918477968764347)
              ·
                refine ⟨9290501179377716953146521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193667452918477968764347 9290501179377716953146521)
                ·
                  refine ⟨6967875884533287714859891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290501179377716953146521 6967875884533287714859891)
                  ·
                    refine ⟨10451813826799931572289837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6967875884533287714859891 10451813826799931572289837)
                    ·
                      refine ⟨3919430185049974339608689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10451813826799931572289837 3919430185049974339608689)
                      ·
                        rfl

theorem cell23_7633063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7633063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633063 prefixEnd_7633063 := by exact prefixLift 7633063
  have htrace : WordTrace (prefixWord ++ tailWord_7633063) baseStart_7633063 baseEnd_7633063 := by
    simpa [prefixWord, tailWord_7633063, baseEnd_7633063] using wordTrace_append hprefix tailTrace_7633063
  have hstable : (prefixWord ++ tailWord_7633063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633063).length < 2 ^ (prefixWord ++ tailWord_7633063).sum := by decide
  have hdescent : baseEnd_7633063 < baseStart_7633063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633068 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_7633068 : Nat := 118140960795 + 7633068 * 2 ^ 59
def prefixEnd_7633068 : Nat := 4983230072969 + 3 ^ 40 * 7633068 * 2
def baseEnd_7633068 : Nat := 3919432752453246820046165

theorem tailTrace_7633068 : CollatzResearch.WordTrace tailWord_7633068 prefixEnd_7633068 3919432752453246820046165 := by
  unfold tailWord_7633068
  simp only [CollatzResearch.WordTrace]
  refine ⟨139200430755352867536341929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185600574340470490048455905 139200430755352867536341929)
  ·
    refine ⟨104400323066514650652256447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139200430755352867536341929 104400323066514650652256447)
    ·
      refine ⟨156600484599771975978384671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104400323066514650652256447 156600484599771975978384671)
      ·
        refine ⟨234900726899657963967577007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156600484599771975978384671 234900726899657963967577007)
        ·
          refine ⟨352351090349486945951365511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234900726899657963967577007 352351090349486945951365511)
          ·
            refine ⟨528526635524230418927048267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352351090349486945951365511 528526635524230418927048267)
            ·
              refine ⟨792789953286345628390572401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528526635524230418927048267 792789953286345628390572401)
              ·
                refine ⟨594592464964759221292929301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792789953286345628390572401 594592464964759221292929301)
                ·
                  refine ⟨27871521795223088498106061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 594592464964759221292929301 27871521795223088498106061)
                  ·
                    refine ⟨10451820673208658186789773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27871521795223088498106061 10451820673208658186789773)
                    ·
                      refine ⟨3919432752453246820046165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10451820673208658186789773 3919432752453246820046165)
                      ·
                        rfl

theorem cell23_7633068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_7633068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633068 prefixEnd_7633068 := by exact prefixLift 7633068
  have htrace : WordTrace (prefixWord ++ tailWord_7633068) baseStart_7633068 baseEnd_7633068 := by
    simpa [prefixWord, tailWord_7633068, baseEnd_7633068] using wordTrace_append hprefix tailTrace_7633068
  have hstable : (prefixWord ++ tailWord_7633068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633068).length < 2 ^ (prefixWord ++ tailWord_7633068).sum := by decide
  have hdescent : baseEnd_7633068 < baseStart_7633068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633098 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_7633098 : Nat := 118140960795 + 7633098 * 2 ^ 59
def prefixEnd_7633098 : Nat := 4983230072969 + 3 ^ 40 * 7633098 * 2
def baseEnd_7633098 : Nat := 3919448156872881702671027

theorem tailTrace_7633098 : CollatzResearch.WordTrace tailWord_7633098 prefixEnd_7633098 3919448156872881702671027 := by
  unfold tailWord_7633098
  simp only [CollatzResearch.WordTrace]
  refine ⟨69600488925149262549068987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185601303800398033464183965 69600488925149262549068987)
  ·
    refine ⟨104400733387723893823603481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69600488925149262549068987 104400733387723893823603481)
    ·
      refine ⟨78300550040792920367702611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104400733387723893823603481 78300550040792920367702611)
      ·
        refine ⟨117450825061189380551553917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78300550040792920367702611 117450825061189380551553917)
        ·
          refine ⟨44044059397946017706832719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117450825061189380551553917 44044059397946017706832719)
          ·
            refine ⟨66066089096919026560249079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44044059397946017706832719 66066089096919026560249079)
            ·
              refine ⟨99099133645378539840373619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66066089096919026560249079 99099133645378539840373619)
              ·
                refine ⟨148648700468067809760560429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99099133645378539840373619 148648700468067809760560429)
                ·
                  refine ⟨55743262675525428660210161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148648700468067809760560429 55743262675525428660210161)
                  ·
                    refine ⟨41807447006644071495157621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55743262675525428660210161 41807447006644071495157621)
                    ·
                      refine ⟨3919448156872881702671027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41807447006644071495157621 3919448156872881702671027)
                      ·
                        rfl

theorem cell23_7633098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_7633098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633098 prefixEnd_7633098 := by exact prefixLift 7633098
  have htrace : WordTrace (prefixWord ++ tailWord_7633098) baseStart_7633098 baseEnd_7633098 := by
    simpa [prefixWord, tailWord_7633098, baseEnd_7633098] using wordTrace_append hprefix tailTrace_7633098
  have hstable : (prefixWord ++ tailWord_7633098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633098).length < 2 ^ (prefixWord ++ tailWord_7633098).sum := by decide
  have hdescent : baseEnd_7633098 < baseStart_7633098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633135 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 5, 4]
def baseStart_7633135 : Nat := 118140960795 + 7633135 * 2 ^ 59
def prefixEnd_7633135 : Nat := 4983230072969 + 3 ^ 40 * 7633135 * 2
def baseEnd_7633135 : Nat := 1306489051885699352636119

theorem tailTrace_7633135 : CollatzResearch.WordTrace tailWord_7633135 prefixEnd_7633135 1306489051885699352636119 := by
  unfold tailWord_7633135
  simp only [CollatzResearch.WordTrace]
  refine ⟨278403305201463005515372859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185602203467642003676915239 278403305201463005515372859)
  ·
    refine ⟨417604957802194508273059289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278403305201463005515372859 417604957802194508273059289)
    ·
      refine ⟨313203718351645881204794467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417604957802194508273059289 313203718351645881204794467)
      ·
        refine ⟨469805577527468821807191701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313203718351645881204794467 469805577527468821807191701)
        ·
          refine ⟨22022136446600101022212111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 469805577527468821807191701 22022136446600101022212111)
          ·
            refine ⟨33033204669900151533318167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22022136446600101022212111 33033204669900151533318167)
            ·
              refine ⟨49549807004850227299977251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33033204669900151533318167 49549807004850227299977251)
              ·
                refine ⟨74324710507275340949965877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49549807004850227299977251 74324710507275340949965877)
                ·
                  refine ⟨6967941610057063214059301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74324710507275340949965877 6967941610057063214059301)
                  ·
                    refine ⟨1306489051885699352636119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967941610057063214059301 1306489051885699352636119)
                    ·
                      rfl

theorem cell23_7633135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_7633135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633135 prefixEnd_7633135 := by exact prefixLift 7633135
  have htrace : WordTrace (prefixWord ++ tailWord_7633135) baseStart_7633135 baseEnd_7633135 := by
    simpa [prefixWord, tailWord_7633135, baseEnd_7633135] using wordTrace_append hprefix tailTrace_7633135
  have hstable : (prefixWord ++ tailWord_7633135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633135).length < 2 ^ (prefixWord ++ tailWord_7633135).sum := by decide
  have hdescent : baseEnd_7633135 < baseStart_7633135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633142 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7633142 : Nat := 118140960795 + 7633142 * 2 ^ 59
def prefixEnd_7633142 : Nat := 4983230072969 + 3 ^ 40 * 7633142 * 2
def baseEnd_7633142 : Nat := 3919470750021679530520825

theorem tailTrace_7633142 : CollatzResearch.WordTrace tailWord_7633142 prefixEnd_7633142 3919470750021679530520825 := by
  unfold tailWord_7633142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17400222532027352856929855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185602373674958430473918453 17400222532027352856929855)
  ·
    refine ⟨26100333798041029285394783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17400222532027352856929855 26100333798041029285394783)
    ·
      refine ⟨39150500697061543928092175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26100333798041029285394783 39150500697061543928092175)
      ·
        refine ⟨58725751045592315892138263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39150500697061543928092175 58725751045592315892138263)
        ·
          refine ⟨88088626568388473838207395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58725751045592315892138263 88088626568388473838207395)
          ·
            refine ⟨132132939852582710757311093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88088626568388473838207395 132132939852582710757311093)
            ·
              refine ⟨12387463111179629133497915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132132939852582710757311093 12387463111179629133497915)
              ·
                refine ⟨18581194666769443700246873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12387463111179629133497915 18581194666769443700246873)
                ·
                  refine ⟨13935896000077082775185155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18581194666769443700246873 13935896000077082775185155)
                  ·
                    refine ⟨20903844000115624162777733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13935896000077082775185155 20903844000115624162777733)
                    ·
                      refine ⟨3919470750021679530520825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20903844000115624162777733 3919470750021679530520825)
                      ·
                        rfl

theorem cell23_7633142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7633142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633142 prefixEnd_7633142 := by exact prefixLift 7633142
  have htrace : WordTrace (prefixWord ++ tailWord_7633142) baseStart_7633142 baseEnd_7633142 := by
    simpa [prefixWord, tailWord_7633142, baseEnd_7633142] using wordTrace_append hprefix tailTrace_7633142
  have hstable : (prefixWord ++ tailWord_7633142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633142).length < 2 ^ (prefixWord ++ tailWord_7633142).sum := by decide
  have hdescent : baseEnd_7633142 < baseStart_7633142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633145 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_7633145 : Nat := 118140960795 + 7633145 * 2 ^ 59
def prefixEnd_7633145 : Nat := 4983230072969 + 3 ^ 40 * 7633145 * 2
def baseEnd_7633145 : Nat := 3919472290463643018783311

theorem tailTrace_7633145 : CollatzResearch.WordTrace tailWord_7633145 prefixEnd_7633145 3919472290463643018783311 := by
  unfold tailWord_7633145
  simp only [CollatzResearch.WordTrace]
  refine ⟨278403669931426777223236889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185602446620951184815491259 278403669931426777223236889)
  ·
    refine ⟨208802752448570082917427667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278403669931426777223236889 208802752448570082917427667)
    ·
      refine ⟨313204128672855124376141501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208802752448570082917427667 313204128672855124376141501)
      ·
        refine ⟨117451548252320671641053063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313204128672855124376141501 117451548252320671641053063)
        ·
          refine ⟨176177322378481007461579595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117451548252320671641053063 176177322378481007461579595)
          ·
            refine ⟨264265983567721511192369393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176177322378481007461579595 264265983567721511192369393)
            ·
              refine ⟨198199487675791133394277045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264265983567721511192369393 198199487675791133394277045)
              ·
                refine ⟨18581201969605418755713473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198199487675791133394277045 18581201969605418755713473)
                ·
                  refine ⟨13935901477204064066785105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18581201969605418755713473 13935901477204064066785105)
                  ·
                    refine ⟨10451926107903048050088829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13935901477204064066785105 10451926107903048050088829)
                    ·
                      refine ⟨3919472290463643018783311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10451926107903048050088829 3919472290463643018783311)
                      ·
                        rfl

theorem cell23_7633145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_7633145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633145 prefixEnd_7633145 := by exact prefixLift 7633145
  have htrace : WordTrace (prefixWord ++ tailWord_7633145) baseStart_7633145 baseEnd_7633145 := by
    simpa [prefixWord, tailWord_7633145, baseEnd_7633145] using wordTrace_append hprefix tailTrace_7633145
  have hstable : (prefixWord ++ tailWord_7633145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633145).length < 2 ^ (prefixWord ++ tailWord_7633145).sum := by decide
  have hdescent : baseEnd_7633145 < baseStart_7633145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633152 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 1, 4]
def baseStart_7633152 : Nat := 118140960795 + 7633152 * 2 ^ 59
def prefixEnd_7633152 : Nat := 4983230072969 + 3 ^ 40 * 7633152 * 2
def baseEnd_7633152 : Nat := 1306491961609408163798593

theorem tailTrace_7633152 : CollatzResearch.WordTrace tailWord_7633152 prefixEnd_7633152 1306491961609408163798593 := by
  unfold tailWord_7633152
  simp only [CollatzResearch.WordTrace]
  refine ⟨139201962621200708709370855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185602616828267611612494473 139201962621200708709370855)
  ·
    refine ⟨208802943931801063064056283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139201962621200708709370855 208802943931801063064056283)
    ·
      refine ⟨313204415897701594596084425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208802943931801063064056283 313204415897701594596084425)
      ·
        refine ⟨234903311923276195947063319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313204415897701594596084425 234903311923276195947063319)
        ·
          refine ⟨352354967884914293920594979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234903311923276195947063319 352354967884914293920594979)
          ·
            refine ⟨528532451827371440880892469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352354967884914293920594979 528532451827371440880892469)
            ·
              refine ⟨49549917358816072582583669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528532451827371440880892469 49549917358816072582583669)
              ·
                refine ⟨4645304752389006804617219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49549917358816072582583669 4645304752389006804617219)
                ·
                  refine ⟨6967957128583510206925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645304752389006804617219 6967957128583510206925829)
                  ·
                    refine ⟨1306491961609408163798593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6967957128583510206925829 1306491961609408163798593)
                    ·
                      rfl

theorem cell23_7633152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 1, 4].length) (baseStart_7633152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633152 prefixEnd_7633152 := by exact prefixLift 7633152
  have htrace : WordTrace (prefixWord ++ tailWord_7633152) baseStart_7633152 baseEnd_7633152 := by
    simpa [prefixWord, tailWord_7633152, baseEnd_7633152] using wordTrace_append hprefix tailTrace_7633152
  have hstable : (prefixWord ++ tailWord_7633152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633152).length < 2 ^ (prefixWord ++ tailWord_7633152).sum := by decide
  have hdescent : baseEnd_7633152 < baseStart_7633152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633252 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_7633252 : Nat := 118140960795 + 7633252 * 2 ^ 59
def prefixEnd_7633252 : Nat := 4983230072969 + 3 ^ 40 * 7633252 * 2
def baseEnd_7633252 : Nat := 3919527232893674100145319

theorem tailTrace_7633252 : CollatzResearch.WordTrace tailWord_7633252 prefixEnd_7633252 3919527232893674100145319 := by
  unfold tailWord_7633252
  simp only [CollatzResearch.WordTrace]
  refine ⟨139203786271019567248691005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185605048361359422998254673 139203786271019567248691005)
  ·
    refine ⟨52201419851632337718259127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139203786271019567248691005 52201419851632337718259127)
    ·
      refine ⟨78302129777448506577388691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52201419851632337718259127 78302129777448506577388691)
      ·
        refine ⟨117453194666172759866083037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78302129777448506577388691 117453194666172759866083037)
        ·
          refine ⟨44044947999814784949781139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117453194666172759866083037 44044947999814784949781139)
          ·
            refine ⟨66067421999722177424671709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44044947999814784949781139 66067421999722177424671709)
            ·
              refine ⟨24775283249895816534251891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66067421999722177424671709 24775283249895816534251891)
              ·
                refine ⟨37162924874843724801377837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24775283249895816534251891 37162924874843724801377837)
                ·
                  refine ⟨13936096828066396800516689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37162924874843724801377837 13936096828066396800516689)
                  ·
                    refine ⟨10452072621049797600387517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13936096828066396800516689 10452072621049797600387517)
                    ·
                      refine ⟨3919527232893674100145319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10452072621049797600387517 3919527232893674100145319)
                      ·
                        rfl

theorem cell23_7633252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_7633252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633252 prefixEnd_7633252 := by exact prefixLift 7633252
  have htrace : WordTrace (prefixWord ++ tailWord_7633252) baseStart_7633252 baseEnd_7633252 := by
    simpa [prefixWord, tailWord_7633252, baseEnd_7633252] using wordTrace_append hprefix tailTrace_7633252
  have hstable : (prefixWord ++ tailWord_7633252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633252).length < 2 ^ (prefixWord ++ tailWord_7633252).sum := by decide
  have hdescent : baseEnd_7633252 < baseStart_7633252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633255 : List Nat := [1, 1, 5, 1, 3, 1, 2, 9]
def baseStart_7633255 : Nat := 118140960795 + 7633255 * 2 ^ 59
def prefixEnd_7633255 : Nat := 4983230072969 + 3 ^ 40 * 7633255 * 2
def baseEnd_7633255 : Nat := 145167732345764355126215

theorem tailTrace_7633255 : CollatzResearch.WordTrace tailWord_7633255 prefixEnd_7633255 145167732345764355126215 := by
  unfold tailWord_7633255
  simp only [CollatzResearch.WordTrace]
  refine ⟨278407681961028266009741219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185605121307352177339827479 278407681961028266009741219)
  ·
    refine ⟨417611522941542399014611829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278407681961028266009741219 417611522941542399014611829)
    ·
      refine ⟨39151080275769599907619859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 417611522941542399014611829 39151080275769599907619859)
      ·
        refine ⟨58726620413654399861429789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39151080275769599907619859 58726620413654399861429789)
        ·
          refine ⟨22022482655120399948036171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58726620413654399861429789 22022482655120399948036171)
          ·
            refine ⟨33033723982680599922054257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22022482655120399948036171 33033723982680599922054257)
            ·
              refine ⟨24775292987010449941540693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33033723982680599922054257 24775292987010449941540693)
              ·
                refine ⟨145167732345764355126215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24775292987010449941540693 145167732345764355126215)
                ·
                  rfl

theorem cell23_7633255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 9].length) (baseStart_7633255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633255 prefixEnd_7633255 := by exact prefixLift 7633255
  have htrace : WordTrace (prefixWord ++ tailWord_7633255) baseStart_7633255 baseEnd_7633255 := by
    simpa [prefixWord, tailWord_7633255, baseEnd_7633255] using wordTrace_append hprefix tailTrace_7633255
  have hstable : (prefixWord ++ tailWord_7633255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633255).length < 2 ^ (prefixWord ++ tailWord_7633255).sum := by decide
  have hdescent : baseEnd_7633255 < baseStart_7633255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633269 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7633269 : Nat := 118140960795 + 7633269 * 2 ^ 59
def prefixEnd_7633269 : Nat := 4983230072969 + 3 ^ 40 * 7633269 * 2
def baseEnd_7633269 : Nat := 3919535962064800533632741

theorem tailTrace_7633269 : CollatzResearch.WordTrace tailWord_7633269 prefixEnd_7633269 3919535962064800533632741 := by
  unfold tailWord_7633269
  simp only [CollatzResearch.WordTrace]
  refine ⟨278408192582977546400750861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185605461721985030933833907 278408192582977546400750861)
  ·
    refine ⟨104403072218616579900281573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278408192582977546400750861 104403072218616579900281573)
    ·
      refine ⟨19575576040990608731302795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104403072218616579900281573 19575576040990608731302795)
      ·
        refine ⟨29363364061485913096954193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19575576040990608731302795 29363364061485913096954193)
        ·
          refine ⟨22022523046114434822715645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29363364061485913096954193 22022523046114434822715645)
          ·
            refine ⟨8258446142292913058518367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22022523046114434822715645 8258446142292913058518367)
            ·
              refine ⟨12387669213439369587777551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258446142292913058518367 12387669213439369587777551)
              ·
                refine ⟨18581503820159054381666327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12387669213439369587777551 18581503820159054381666327)
                ·
                  refine ⟨27872255730238581572499491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18581503820159054381666327 27872255730238581572499491)
                  ·
                    refine ⟨41808383595357872358749237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27872255730238581572499491 41808383595357872358749237)
                    ·
                      refine ⟨3919535962064800533632741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41808383595357872358749237 3919535962064800533632741)
                      ·
                        rfl

theorem cell23_7633269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7633269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633269 prefixEnd_7633269 := by exact prefixLift 7633269
  have htrace : WordTrace (prefixWord ++ tailWord_7633269) baseStart_7633269 baseEnd_7633269 := by
    simpa [prefixWord, tailWord_7633269, baseEnd_7633269] using wordTrace_append hprefix tailTrace_7633269
  have hstable : (prefixWord ++ tailWord_7633269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633269).length < 2 ^ (prefixWord ++ tailWord_7633269).sum := by decide
  have hdescent : baseEnd_7633269 < baseStart_7633269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633283 : List Nat := [1, 1, 1, 3, 6, 1, 1, 4, 1, 2, 2]
def baseStart_7633283 : Nat := 118140960795 + 7633283 * 2 ^ 59
def prefixEnd_7633283 : Nat := 4983230072969 + 3 ^ 40 * 7633283 * 2
def baseEnd_7633283 : Nat := 3919543150793963478857677

theorem tailTrace_7633283 : CollatzResearch.WordTrace tailWord_7633283 prefixEnd_7633283 3919543150793963478857677 := by
  unfold tailWord_7633283
  simp only [CollatzResearch.WordTrace]
  refine ⟨278408703204926826791760503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185605802136617884527840335 278408703204926826791760503)
  ·
    refine ⟨417613054807390240187640755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278408703204926826791760503 417613054807390240187640755)
    ·
      refine ⟨626419582211085360281461133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417613054807390240187640755 626419582211085360281461133)
      ·
        refine ⟨234907343329157010105547925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626419582211085360281461133 234907343329157010105547925)
        ·
          refine ⟨11011281718554234848697559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234907343329157010105547925 11011281718554234848697559)
          ·
            refine ⟨16516922577831352273046339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11011281718554234848697559 16516922577831352273046339)
            ·
              refine ⟨24775383866747028409569509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16516922577831352273046339 24775383866747028409569509)
              ·
                refine ⟨4645384475015067826794283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24775383866747028409569509 4645384475015067826794283)
                ·
                  refine ⟨6968076712522601740191425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645384475015067826794283 6968076712522601740191425)
                  ·
                    refine ⟨5226057534391951305143569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6968076712522601740191425 5226057534391951305143569)
                    ·
                      refine ⟨3919543150793963478857677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226057534391951305143569 3919543150793963478857677)
                      ·
                        rfl

theorem cell23_7633283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_7633283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633283 prefixEnd_7633283 := by exact prefixLift 7633283
  have htrace : WordTrace (prefixWord ++ tailWord_7633283) baseStart_7633283 baseEnd_7633283 := by
    simpa [prefixWord, tailWord_7633283, baseEnd_7633283] using wordTrace_append hprefix tailTrace_7633283
  have hstable : (prefixWord ++ tailWord_7633283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633283).length < 2 ^ (prefixWord ++ tailWord_7633283).sum := by decide
  have hdescent : baseEnd_7633283 < baseStart_7633283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633305 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_7633305 : Nat := 118140960795 + 7633305 * 2 ^ 59
def prefixEnd_7633305 : Nat := 4983230072969 + 3 ^ 40 * 7633305 * 2
def baseEnd_7633305 : Nat := 3919554447368362392782575

theorem tailTrace_7633305 : CollatzResearch.WordTrace tailWord_7633305 prefixEnd_7633305 3919554447368362392782575 := by
  unfold tailWord_7633305
  simp only [CollatzResearch.WordTrace]
  refine ⟨278409505610847124549061369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185606337073898083032707579 278409505610847124549061369)
  ·
    refine ⟨208807129208135343411796027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278409505610847124549061369 208807129208135343411796027)
    ·
      refine ⟨313210693812203015117694041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208807129208135343411796027 313210693812203015117694041)
      ·
        refine ⟨234908020359152261338270531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313210693812203015117694041 234908020359152261338270531)
        ·
          refine ⟨352362030538728392007405797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234908020359152261338270531 352362030538728392007405797)
          ·
            refine ⟨66067880726011573501388587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352362030538728392007405797 66067880726011573501388587)
            ·
              refine ⟨99101821089017360252082881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66067880726011573501388587 99101821089017360252082881)
              ·
                refine ⟨74326365816763020189062161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99101821089017360252082881 74326365816763020189062161)
                ·
                  refine ⟨55744774362572265141796621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74326365816763020189062161 55744774362572265141796621)
                  ·
                    refine ⟨20904290385964599428173733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55744774362572265141796621 20904290385964599428173733)
                    ·
                      refine ⟨3919554447368362392782575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20904290385964599428173733 3919554447368362392782575)
                      ·
                        rfl

theorem cell23_7633305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_7633305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633305 prefixEnd_7633305 := by exact prefixLift 7633305
  have htrace : WordTrace (prefixWord ++ tailWord_7633305) baseStart_7633305 baseEnd_7633305 := by
    simpa [prefixWord, tailWord_7633305, baseEnd_7633305] using wordTrace_append hprefix tailTrace_7633305
  have hstable : (prefixWord ++ tailWord_7633305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633305).length < 2 ^ (prefixWord ++ tailWord_7633305).sum := by decide
  have hdescent : baseEnd_7633305 < baseStart_7633305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633333 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_7633333 : Nat := 118140960795 + 7633333 * 2 ^ 59
def prefixEnd_7633333 : Nat := 4983230072969 + 3 ^ 40 * 7633333 * 2
def baseEnd_7633333 : Nat := 3919568824826688283232447

theorem tailTrace_7633333 : CollatzResearch.WordTrace tailWord_7633333 prefixEnd_7633333 3919568824826688283232447 := by
  unfold tailWord_7633333
  simp only [CollatzResearch.WordTrace]
  refine ⟨278410526854745685331080653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185607017903163790220720435 278410526854745685331080653)
  ·
    refine ⟨104403947570529631999155245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278410526854745685331080653 104403947570529631999155245)
    ·
      refine ⟨39151480338948611999683217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104403947570529631999155245 39151480338948611999683217)
      ·
        refine ⟨29363610254211458999762413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39151480338948611999683217 29363610254211458999762413)
        ·
          refine ⟨11011353845329297124910905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29363610254211458999762413 11011353845329297124910905)
          ·
            refine ⟨8258515383996972843683179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11011353845329297124910905 8258515383996972843683179)
            ·
              refine ⟨12387773075995459265524769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258515383996972843683179 12387773075995459265524769)
              ·
                refine ⟨9290829806996594449143577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12387773075995459265524769 9290829806996594449143577)
                ·
                  refine ⟨6968122355247445836857683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290829806996594449143577 6968122355247445836857683)
                  ·
                    refine ⟨10452183532871168755286525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6968122355247445836857683 10452183532871168755286525)
                    ·
                      refine ⟨3919568824826688283232447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10452183532871168755286525 3919568824826688283232447)
                      ·
                        rfl

theorem cell23_7633333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_7633333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633333 prefixEnd_7633333 := by exact prefixLift 7633333
  have htrace : WordTrace (prefixWord ++ tailWord_7633333) baseStart_7633333 baseEnd_7633333 := by
    simpa [prefixWord, tailWord_7633333, baseEnd_7633333] using wordTrace_append hprefix tailTrace_7633333
  have hstable : (prefixWord ++ tailWord_7633333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633333).length < 2 ^ (prefixWord ++ tailWord_7633333).sum := by decide
  have hdescent : baseEnd_7633333 < baseStart_7633333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633342 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_7633342 : Nat := 118140960795 + 7633342 * 2 ^ 59
def prefixEnd_7633342 : Nat := 4983230072969 + 3 ^ 40 * 7633342 * 2
def baseEnd_7633342 : Nat := 3919573446152578748019905

theorem tailTrace_7633342 : CollatzResearch.WordTrace tailWord_7633342 prefixEnd_7633342 3919573446152578748019905 := by
  unfold tailWord_7633342
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801356888964134983519785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185607236741142053245438853 34801356888964134983519785)
  ·
    refine ⟨26101017666723101237639839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34801356888964134983519785 26101017666723101237639839)
    ·
      refine ⟨39151526500084651856459759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26101017666723101237639839 39151526500084651856459759)
      ·
        refine ⟨58727289750126977784689639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39151526500084651856459759 58727289750126977784689639)
        ·
          refine ⟨88090934625190466677034459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58727289750126977784689639 88090934625190466677034459)
          ·
            refine ⟨132136401937785700015551689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88090934625190466677034459 132136401937785700015551689)
            ·
              refine ⟨99102301453339275011663767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132136401937785700015551689 99102301453339275011663767)
              ·
                refine ⟨148653452180008912517495651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99102301453339275011663767 148653452180008912517495651)
                ·
                  refine ⟨222980178270013368776243477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148653452180008912517495651 222980178270013368776243477)
                  ·
                    refine ⟨10452195856406876661386413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222980178270013368776243477 10452195856406876661386413)
                    ·
                      refine ⟨3919573446152578748019905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10452195856406876661386413 3919573446152578748019905)
                      ·
                        rfl

theorem cell23_7633342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_7633342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633342 prefixEnd_7633342 := by exact prefixLift 7633342
  have htrace : WordTrace (prefixWord ++ tailWord_7633342) baseStart_7633342 baseEnd_7633342 := by
    simpa [prefixWord, tailWord_7633342, baseEnd_7633342] using wordTrace_append hprefix tailTrace_7633342
  have hstable : (prefixWord ++ tailWord_7633342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633342).length < 2 ^ (prefixWord ++ tailWord_7633342).sum := by decide
  have hdescent : baseEnd_7633342 < baseStart_7633342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633352 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_7633352 : Nat := 118140960795 + 7633352 * 2 ^ 59
def prefixEnd_7633352 : Nat := 4983230072969 + 3 ^ 40 * 7633352 * 2
def baseEnd_7633352 : Nat := 3919578580959123708894859

theorem tailTrace_7633352 : CollatzResearch.WordTrace tailWord_7633352 prefixEnd_7633352 3919578580959123708894859 := by
  unfold tailWord_7633352
  simp only [CollatzResearch.WordTrace]
  refine ⟨139205609920838425788011155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185607479894451234384014873 139205609920838425788011155)
  ·
    refine ⟨208808414881257638682016733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139205609920838425788011155 208808414881257638682016733)
    ·
      refine ⟨78303155580471614505756275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208808414881257638682016733 78303155580471614505756275)
      ·
        refine ⟨117454733370707421758634413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78303155580471614505756275 117454733370707421758634413)
        ·
          refine ⟨44045525014015283159487905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117454733370707421758634413 44045525014015283159487905)
          ·
            refine ⟨33034143760511462369615929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44045525014015283159487905 33034143760511462369615929)
            ·
              refine ⟨24775607820383596777211947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33034143760511462369615929 24775607820383596777211947)
              ·
                refine ⟨37163411730575395165817921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24775607820383596777211947 37163411730575395165817921)
                ·
                  refine ⟨27872558797931546374363441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37163411730575395165817921 27872558797931546374363441)
                  ·
                    refine ⟨20904419098448659780772581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27872558797931546374363441 20904419098448659780772581)
                    ·
                      refine ⟨3919578580959123708894859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20904419098448659780772581 3919578580959123708894859)
                      ·
                        rfl

theorem cell23_7633352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_7633352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633352 prefixEnd_7633352 := by exact prefixLift 7633352
  have htrace : WordTrace (prefixWord ++ tailWord_7633352) baseStart_7633352 baseEnd_7633352 := by
    simpa [prefixWord, tailWord_7633352, baseEnd_7633352] using wordTrace_append hprefix tailTrace_7633352
  have hstable : (prefixWord ++ tailWord_7633352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633352).length < 2 ^ (prefixWord ++ tailWord_7633352).sum := by decide
  have hdescent : baseEnd_7633352 < baseStart_7633352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633392 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_7633392 : Nat := 118140960795 + 7633392 * 2 ^ 59
def prefixEnd_7633392 : Nat := 4983230072969 + 3 ^ 40 * 7633392 * 2
def baseEnd_7633392 : Nat := 1306533040061767850798225

theorem tailTrace_7633392 : CollatzResearch.WordTrace tailWord_7633392 prefixEnd_7633392 1306533040061767850798225 := by
  unfold tailWord_7633392
  simp only [CollatzResearch.WordTrace]
  refine ⟨139206339380765969203739215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185608452507687958938318953 139206339380765969203739215)
  ·
    refine ⟨208809509071148953805608823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139206339380765969203739215 208809509071148953805608823)
    ·
      refine ⟨313214263606723430708413235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208809509071148953805608823 313214263606723430708413235)
      ·
        refine ⟨469821395410085146062619853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313214263606723430708413235 469821395410085146062619853)
        ·
          refine ⟨176183023278781929773482445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469821395410085146062619853 176183023278781929773482445)
          ·
            refine ⟨66068633729543223665055917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176183023278781929773482445 66068633729543223665055917)
            ·
              refine ⟨24775737648578708874395969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66068633729543223665055917 24775737648578708874395969)
              ·
                refine ⟨18581803236434031655796977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24775737648578708874395969 18581803236434031655796977)
                ·
                  refine ⟨13936352427325523741847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18581803236434031655796977 13936352427325523741847733)
                  ·
                    refine ⟨1306533040061767850798225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13936352427325523741847733 1306533040061767850798225)
                    ·
                      rfl

theorem cell23_7633392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_7633392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633392 prefixEnd_7633392 := by exact prefixLift 7633392
  have htrace : WordTrace (prefixWord ++ tailWord_7633392) baseStart_7633392 baseEnd_7633392 := by
    simpa [prefixWord, tailWord_7633392, baseEnd_7633392] using wordTrace_append hprefix tailTrace_7633392
  have hstable : (prefixWord ++ tailWord_7633392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633392).length < 2 ^ (prefixWord ++ tailWord_7633392).sum := by decide
  have hdescent : baseEnd_7633392 < baseStart_7633392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633429 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_7633429 : Nat := 118140960795 + 7633429 * 2 ^ 59
def prefixEnd_7633429 : Nat := 4983230072969 + 3 ^ 40 * 7633429 * 2
def baseEnd_7633429 : Nat := 3919618118969519907632005

theorem tailTrace_7633429 : CollatzResearch.WordTrace tailWord_7633429 prefixEnd_7633429 3919618118969519907632005 := by
  unfold tailWord_7633429
  simp only [CollatzResearch.WordTrace]
  refine ⟨278414028262397893726575341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185609352174931929151050227 278414028262397893726575341)
  ·
    refine ⟨104405260598399210147465753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278414028262397893726575341 104405260598399210147465753)
    ·
      refine ⟨78303945448799407610599315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104405260598399210147465753 78303945448799407610599315)
      ·
        refine ⟨117455918173199111415898973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78303945448799407610599315 117455918173199111415898973)
        ·
          refine ⟨44045969314949666780962115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117455918173199111415898973 44045969314949666780962115)
          ·
            refine ⟨66068953972424500171443173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44045969314949666780962115 66068953972424500171443173)
            ·
              refine ⟨12387928869829593782145595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66068953972424500171443173 12387928869829593782145595)
              ·
                refine ⟨18581893304744390673218393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12387928869829593782145595 18581893304744390673218393)
                ·
                  refine ⟨13936419978558293004913795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18581893304744390673218393 13936419978558293004913795)
                  ·
                    refine ⟨20904629967837439507370693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13936419978558293004913795 20904629967837439507370693)
                    ·
                      refine ⟨3919618118969519907632005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20904629967837439507370693 3919618118969519907632005)
                      ·
                        rfl

theorem cell23_7633429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_7633429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633429 prefixEnd_7633429 := by exact prefixLift 7633429
  have htrace : WordTrace (prefixWord ++ tailWord_7633429) baseStart_7633429 baseEnd_7633429 := by
    simpa [prefixWord, tailWord_7633429, baseEnd_7633429] using wordTrace_append hprefix tailTrace_7633429
  have hstable : (prefixWord ++ tailWord_7633429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633429).length < 2 ^ (prefixWord ++ tailWord_7633429).sum := by decide
  have hdescent : baseEnd_7633429 < baseStart_7633429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633442 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7633442 : Nat := 118140960795 + 7633442 * 2 ^ 59
def prefixEnd_7633442 : Nat := 4983230072969 + 3 ^ 40 * 7633442 * 2
def baseEnd_7633442 : Nat := 3919624794218028356769445

theorem tailTrace_7633442 : CollatzResearch.WordTrace tailWord_7633442 prefixEnd_7633442 3919624794218028356769445 := by
  unfold tailWord_7633442
  simp only [CollatzResearch.WordTrace]
  refine ⟨69603625602837699236699645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185609668274233864631199053 69603625602837699236699645)
  ·
    refine ⟨26101359601064137213762367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69603625602837699236699645 26101359601064137213762367)
    ·
      refine ⟨39152039401596205820643551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26101359601064137213762367 39152039401596205820643551)
      ·
        refine ⟨58728059102394308730965327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39152039401596205820643551 58728059102394308730965327)
        ·
          refine ⟨88092088653591463096447991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58728059102394308730965327 88092088653591463096447991)
          ·
            refine ⟨132138132980387194644671987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88092088653591463096447991 132138132980387194644671987)
            ·
              refine ⟨198207199470580791967007981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132138132980387194644671987 198207199470580791967007981)
              ·
                refine ⟨74327699801467796987627993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198207199470580791967007981 74327699801467796987627993)
                ·
                  refine ⟨55745774851100847740720995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74327699801467796987627993 55745774851100847740720995)
                  ·
                    refine ⟨83618662276651271611081493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55745774851100847740720995 83618662276651271611081493)
                    ·
                      refine ⟨3919624794218028356769445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83618662276651271611081493 3919624794218028356769445)
                      ·
                        rfl

theorem cell23_7633442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7633442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633442 prefixEnd_7633442 := by exact prefixLift 7633442
  have htrace : WordTrace (prefixWord ++ tailWord_7633442) baseStart_7633442 baseEnd_7633442 := by
    simpa [prefixWord, tailWord_7633442, baseEnd_7633442] using wordTrace_append hprefix tailTrace_7633442
  have hstable : (prefixWord ++ tailWord_7633442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633442).length < 2 ^ (prefixWord ++ tailWord_7633442).sum := by decide
  have hdescent : baseEnd_7633442 < baseStart_7633442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633447 : List Nat := [1, 1, 7, 2, 2, 1, 2, 2, 5]
def baseStart_7633447 : Nat := 118140960795 + 7633447 * 2 ^ 59
def prefixEnd_7633447 : Nat := 4983230072969 + 3 ^ 40 * 7633447 * 2
def baseEnd_7633447 : Nat := 435514151291255648578547

theorem tailTrace_7633447 : CollatzResearch.WordTrace tailWord_7633447 prefixEnd_7633447 435514151291255648578547 := by
  unfold tailWord_7633447
  simp only [CollatzResearch.WordTrace]
  refine ⟨278414684776332682800730595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185609789850888455200487063 278414684776332682800730595)
  ·
    refine ⟨417622027164499024201095893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278414684776332682800730595 417622027164499024201095893)
    ·
      refine ⟨9788016261667945879713185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 417622027164499024201095893 9788016261667945879713185)
      ·
        refine ⟨7341012196250959409784889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9788016261667945879713185 7341012196250959409784889)
        ·
          refine ⟨5505759147188219557338667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7341012196250959409784889 5505759147188219557338667)
          ·
            refine ⟨8258638720782329336008001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505759147188219557338667 8258638720782329336008001)
            ·
              refine ⟨6193979040586747002006001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8258638720782329336008001 6193979040586747002006001)
              ·
                refine ⟨4645484280440060251504501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6193979040586747002006001 4645484280440060251504501)
                ·
                  refine ⟨435514151291255648578547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645484280440060251504501 435514151291255648578547)
                  ·
                    rfl

theorem cell23_7633447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 5].length) (baseStart_7633447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633447 prefixEnd_7633447 := by exact prefixLift 7633447
  have htrace : WordTrace (prefixWord ++ tailWord_7633447) baseStart_7633447 baseEnd_7633447 := by
    simpa [prefixWord, tailWord_7633447, baseEnd_7633447] using wordTrace_append hprefix tailTrace_7633447
  have hstable : (prefixWord ++ tailWord_7633447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633447).length < 2 ^ (prefixWord ++ tailWord_7633447).sum := by decide
  have hdescent : baseEnd_7633447 < baseStart_7633447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633469 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 6]
def baseStart_7633469 : Nat := 118140960795 + 7633469 * 2 ^ 59
def prefixEnd_7633469 : Nat := 4983230072969 + 3 ^ 40 * 7633469 * 2
def baseEnd_7633469 : Nat := 435515406466188861236869

theorem tailTrace_7633469 : CollatzResearch.WordTrace tailWord_7633469 prefixEnd_7633469 435515406466188861236869 := by
  unfold tailWord_7633469
  simp only [CollatzResearch.WordTrace]
  refine ⟨278415487182252980558031461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185610324788168653705354307 278415487182252980558031461)
  ·
    refine ⟨52202903846672433854630899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278415487182252980558031461 52202903846672433854630899)
    ·
      refine ⟨78304355770008650781946349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52202903846672433854630899 78304355770008650781946349)
      ·
        refine ⟨29364133413753244043229881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78304355770008650781946349 29364133413753244043229881)
        ·
          refine ⟨22023100060314933032422411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29364133413753244043229881 22023100060314933032422411)
          ·
            refine ⟨33034650090472399548633617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22023100060314933032422411 33034650090472399548633617)
            ·
              refine ⟨24775987567854299661475213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33034650090472399548633617 24775987567854299661475213)
              ·
                refine ⟨9290995337945362373053205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24775987567854299661475213 9290995337945362373053205)
                ·
                  refine ⟨435515406466188861236869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9290995337945362373053205 435515406466188861236869)
                  ·
                    rfl

theorem cell23_7633469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_7633469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633469 prefixEnd_7633469 := by exact prefixLift 7633469
  have htrace : WordTrace (prefixWord ++ tailWord_7633469) baseStart_7633469 baseEnd_7633469 := by
    simpa [prefixWord, tailWord_7633469, baseEnd_7633469] using wordTrace_append hprefix tailTrace_7633469
  have hstable : (prefixWord ++ tailWord_7633469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633469).length < 2 ^ (prefixWord ++ tailWord_7633469).sum := by decide
  have hdescent : baseEnd_7633469 < baseStart_7633469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633529 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_7633529 : Nat := 118140960795 + 7633529 * 2 ^ 59
def prefixEnd_7633529 : Nat := 4983230072969 + 3 ^ 40 * 7633529 * 2
def baseEnd_7633529 : Nat := 1306556489011656505460515

theorem tailTrace_7633529 : CollatzResearch.WordTrace tailWord_7633529 prefixEnd_7633529 1306556489011656505460515 := by
  unfold tailWord_7633529
  simp only [CollatzResearch.WordTrace]
  refine ⟨278417675562035610805215641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185611783708023740536810427 278417675562035610805215641)
  ·
    refine ⟨208813256671526708103911731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278417675562035610805215641 208813256671526708103911731)
    ·
      refine ⟨313219885007290062155867597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208813256671526708103911731 313219885007290062155867597)
      ·
        refine ⟨117457456877733773308450349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313219885007290062155867597 117457456877733773308450349)
        ·
          refine ⟨44046546329150164990668881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117457456877733773308450349 44046546329150164990668881)
          ·
            refine ⟨33034909746862623743001661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44046546329150164990668881 33034909746862623743001661)
            ·
              refine ⟨12388091155073483903625623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33034909746862623743001661 12388091155073483903625623)
              ·
                refine ⟨18582136732610225855438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12388091155073483903625623 18582136732610225855438435)
                ·
                  refine ⟨27873205098915338783157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18582136732610225855438435 27873205098915338783157653)
                  ·
                    refine ⟨1306556489011656505460515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27873205098915338783157653 1306556489011656505460515)
                    ·
                      rfl

theorem cell23_7633529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_7633529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633529 prefixEnd_7633529 := by exact prefixLift 7633529
  have htrace : WordTrace (prefixWord ++ tailWord_7633529) baseStart_7633529 baseEnd_7633529 := by
    simpa [prefixWord, tailWord_7633529, baseEnd_7633529] using wordTrace_append hprefix tailTrace_7633529
  have hstable : (prefixWord ++ tailWord_7633529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633529).length < 2 ^ (prefixWord ++ tailWord_7633529).sum := by decide
  have hdescent : baseEnd_7633529 < baseStart_7633529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633536 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_7633536 : Nat := 118140960795 + 7633536 * 2 ^ 59
def prefixEnd_7633536 : Nat := 4983230072969 + 3 ^ 40 * 7633536 * 2
def baseEnd_7633536 : Nat := 3919673061399550988994013

theorem tailTrace_7633536 : CollatzResearch.WordTrace tailWord_7633536 prefixEnd_7633536 3919673061399550988994013 := by
  unfold tailWord_7633536
  simp only [CollatzResearch.WordTrace]
  refine ⟨139208965436505125500360231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185611953915340167333813641 139208965436505125500360231)
  ·
    refine ⟨208813448154757688250540347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139208965436505125500360231 208813448154757688250540347)
    ·
      refine ⟨313220172232136532375810521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208813448154757688250540347 313220172232136532375810521)
      ·
        refine ⟨234915129174102399281857891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313220172232136532375810521 234915129174102399281857891)
        ·
          refine ⟨352372693761153598922786837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234915129174102399281857891 352372693761153598922786837)
          ·
            refine ⟨16517470020054074949505633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352372693761153598922786837 16517470020054074949505633)
            ·
              refine ⟨12388102515040556212129225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16517470020054074949505633 12388102515040556212129225)
              ·
                refine ⟨9291076886280417159096919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12388102515040556212129225 9291076886280417159096919)
                ·
                  refine ⟨13936615329420625738645379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291076886280417159096919 13936615329420625738645379)
                  ·
                    refine ⟨20904922994130938607968069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13936615329420625738645379 20904922994130938607968069)
                    ·
                      refine ⟨3919673061399550988994013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20904922994130938607968069 3919673061399550988994013)
                      ·
                        rfl

theorem cell23_7633536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_7633536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633536 prefixEnd_7633536 := by exact prefixLift 7633536
  have htrace : WordTrace (prefixWord ++ tailWord_7633536) baseStart_7633536 baseEnd_7633536 := by
    simpa [prefixWord, tailWord_7633536, baseEnd_7633536] using wordTrace_append hprefix tailTrace_7633536
  have hstable : (prefixWord ++ tailWord_7633536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633536).length < 2 ^ (prefixWord ++ tailWord_7633536).sum := by decide
  have hdescent : baseEnd_7633536 < baseStart_7633536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633539 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3]
def baseStart_7633539 : Nat := 118140960795 + 7633539 * 2 ^ 59
def prefixEnd_7633539 : Nat := 4983230072969 + 3 ^ 40 * 7633539 * 2
def baseEnd_7633539 : Nat := 3919674601841514477256499

theorem tailTrace_7633539 : CollatzResearch.WordTrace tailWord_7633539 prefixEnd_7633539 3919674601841514477256499 := by
  unfold tailWord_7633539
  simp only [CollatzResearch.WordTrace]
  refine ⟨278418040291999382513079671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185612026861332921675386447 278418040291999382513079671)
  ·
    refine ⟨417627060437999073769619507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278418040291999382513079671 417627060437999073769619507)
    ·
      refine ⟨626440590656998610654429261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417627060437999073769619507 626440590656998610654429261)
      ·
        refine ⟨234915221496374478995410973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626440590656998610654429261 234915221496374478995410973)
        ·
          refine ⟨88093208061140429623279115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234915221496374478995410973 88093208061140429623279115)
          ·
            refine ⟨132139812091710644434918673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88093208061140429623279115 132139812091710644434918673)
            ·
              refine ⟨99104859068782983326189005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132139812091710644434918673 99104859068782983326189005)
              ·
                refine ⟨37164322150793618747320877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99104859068782983326189005 37164322150793618747320877)
                ·
                  refine ⟨13936620806547607030245329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37164322150793618747320877 13936620806547607030245329)
                  ·
                    refine ⟨10452465604910705272683997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13936620806547607030245329 10452465604910705272683997)
                    ·
                      refine ⟨3919674601841514477256499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10452465604910705272683997 3919674601841514477256499)
                      ·
                        rfl

theorem cell23_7633539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_7633539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633539 prefixEnd_7633539 := by exact prefixLift 7633539
  have htrace : WordTrace (prefixWord ++ tailWord_7633539) baseStart_7633539 baseEnd_7633539 := by
    simpa [prefixWord, tailWord_7633539, baseEnd_7633539] using wordTrace_append hprefix tailTrace_7633539
  have hstable : (prefixWord ++ tailWord_7633539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633539).length < 2 ^ (prefixWord ++ tailWord_7633539).sum := by decide
  have hdescent : baseEnd_7633539 < baseStart_7633539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633556 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7633556 : Nat := 118140960795 + 7633556 * 2 ^ 59
def prefixEnd_7633556 : Nat := 4983230072969 + 3 ^ 40 * 7633556 * 2
def baseEnd_7633556 : Nat := 3919683331012640910743921

theorem tailTrace_7633556 : CollatzResearch.WordTrace tailWord_7633556 prefixEnd_7633556 3919683331012640910743921 := by
  unfold tailWord_7633556
  simp only [CollatzResearch.WordTrace]
  refine ⟨139209330166468897208224261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185612440221958529610965681 139209330166468897208224261)
  ·
    refine ⟨26101749406212918226542049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139209330166468897208224261 26101749406212918226542049)
    ·
      refine ⟨19576312054659688669906537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26101749406212918226542049 19576312054659688669906537)
      ·
        refine ⟨14682234040994766502429903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19576312054659688669906537 14682234040994766502429903)
        ·
          refine ⟨22023351061492149753644855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14682234040994766502429903 22023351061492149753644855)
          ·
            refine ⟨33035026592238224630467283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22023351061492149753644855 33035026592238224630467283)
            ·
              refine ⟨49552539888357336945700925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33035026592238224630467283 49552539888357336945700925)
              ·
                refine ⟨18582202458134001354637847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49552539888357336945700925 18582202458134001354637847)
                ·
                  refine ⟨27873303687201002031956771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18582202458134001354637847 27873303687201002031956771)
                  ·
                    refine ⟨41809955530801503047935157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27873303687201002031956771 41809955530801503047935157)
                    ·
                      refine ⟨3919683331012640910743921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41809955530801503047935157 3919683331012640910743921)
                      ·
                        rfl

theorem cell23_7633556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7633556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633556 prefixEnd_7633556 := by exact prefixLift 7633556
  have htrace : WordTrace (prefixWord ++ tailWord_7633556) baseStart_7633556 baseEnd_7633556 := by
    simpa [prefixWord, tailWord_7633556, baseEnd_7633556] using wordTrace_append hprefix tailTrace_7633556
  have hstable : (prefixWord ++ tailWord_7633556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633556).length < 2 ^ (prefixWord ++ tailWord_7633556).sum := by decide
  have hdescent : baseEnd_7633556 < baseStart_7633556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633590 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_7633590 : Nat := 118140960795 + 7633590 * 2 ^ 59
def prefixEnd_7633590 : Nat := 4983230072969 + 3 ^ 40 * 7633590 * 2
def baseEnd_7633590 : Nat := 3919700789354893777718765

theorem tailTrace_7633590 : CollatzResearch.WordTrace tailWord_7633590 prefixEnd_7633590 3919700789354893777718765 := by
  unfold tailWord_7633590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17401243775925913638949139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185613266943209745482124149 17401243775925913638949139)
  ·
    refine ⟨26101865663888870458423709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17401243775925913638949139 26101865663888870458423709)
    ·
      refine ⟨9788199623958326421908891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26101865663888870458423709 9788199623958326421908891)
      ·
        refine ⟨14682299435937489632863337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788199623958326421908891 14682299435937489632863337)
        ·
          refine ⟨11011724576953117224647503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14682299435937489632863337 11011724576953117224647503)
          ·
            refine ⟨16517586865429675836971255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11011724576953117224647503 16517586865429675836971255)
            ·
              refine ⟨24776380298144513755456883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16517586865429675836971255 24776380298144513755456883)
              ·
                refine ⟨37164570447216770633185325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24776380298144513755456883 37164570447216770633185325)
                ·
                  refine ⟨13936713917706288987444497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37164570447216770633185325 13936713917706288987444497)
                  ·
                    refine ⟨10452535438279716740583373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13936713917706288987444497 10452535438279716740583373)
                    ·
                      refine ⟨3919700789354893777718765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10452535438279716740583373 3919700789354893777718765)
                      ·
                        rfl

theorem cell23_7633590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_7633590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633590 prefixEnd_7633590 := by exact prefixLift 7633590
  have htrace : WordTrace (prefixWord ++ tailWord_7633590) baseStart_7633590 baseEnd_7633590 := by
    simpa [prefixWord, tailWord_7633590, baseEnd_7633590] using wordTrace_append hprefix tailTrace_7633590
  have hstable : (prefixWord ++ tailWord_7633590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633590).length < 2 ^ (prefixWord ++ tailWord_7633590).sum := by decide
  have hdescent : baseEnd_7633590 < baseStart_7633590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633592 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_7633592 : Nat := 118140960795 + 7633592 * 2 ^ 59
def prefixEnd_7633592 : Nat := 4983230072969 + 3 ^ 40 * 7633592 * 2
def baseEnd_7633592 : Nat := 3919701816316202769893755

theorem tailTrace_7633592 : CollatzResearch.WordTrace tailWord_7633592 prefixEnd_7633592 3919701816316202769893755 := by
  unfold tailWord_7633592
  simp only [CollatzResearch.WordTrace]
  refine ⟨139209986680403686282379515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185613315573871581709839353 139209986680403686282379515)
  ·
    refine ⟨208814980020605529423569273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139209986680403686282379515 208814980020605529423569273)
    ·
      refine ⟨156611235015454147067676955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208814980020605529423569273 156611235015454147067676955)
      ·
        refine ⟨234916852523181220601515433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156611235015454147067676955 234916852523181220601515433)
        ·
          refine ⟨176187639392385915451136575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234916852523181220601515433 176187639392385915451136575)
          ·
            refine ⟨264281459088578873176704863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176187639392385915451136575 264281459088578873176704863)
            ·
              refine ⟨396422188632868309765057295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264281459088578873176704863 396422188632868309765057295)
              ·
                refine ⟨594633282949302464647585943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396422188632868309765057295 594633282949302464647585943)
                ·
                  refine ⟨891949924423953696971378915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594633282949302464647585943 891949924423953696971378915)
                  ·
                    refine ⟨1337924886635930545457068373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891949924423953696971378915 1337924886635930545457068373)
                    ·
                      refine ⟨3919701816316202769893755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1337924886635930545457068373 3919701816316202769893755)
                      ·
                        rfl

theorem cell23_7633592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_7633592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633592 prefixEnd_7633592 := by exact prefixLift 7633592
  have htrace : WordTrace (prefixWord ++ tailWord_7633592) baseStart_7633592 baseEnd_7633592 := by
    simpa [prefixWord, tailWord_7633592, baseEnd_7633592] using wordTrace_append hprefix tailTrace_7633592
  have hstable : (prefixWord ++ tailWord_7633592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633592).length < 2 ^ (prefixWord ++ tailWord_7633592).sum := by decide
  have hdescent : baseEnd_7633592 < baseStart_7633592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633621 : List Nat := [1, 3, 2, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7633621 : Nat := 118140960795 + 7633621 * 2 ^ 59
def prefixEnd_7633621 : Nat := 4983230072969 + 3 ^ 40 * 7633621 * 2
def baseEnd_7633621 : Nat := 3919716707255183156431123

theorem tailTrace_7633621 : CollatzResearch.WordTrace tailWord_7633621 prefixEnd_7633621 3919716707255183156431123 := by
  unfold tailWord_7633621
  simp only [CollatzResearch.WordTrace]
  refine ⟨278421031077702310517564717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185614020718468207011709811 278421031077702310517564717)
  ·
    refine ⟨104407886654138366444086769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278421031077702310517564717 104407886654138366444086769)
    ·
      refine ⟨78305914990603774833065077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104407886654138366444086769 78305914990603774833065077)
      ·
        refine ⟨7341179530369103890599851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78305914990603774833065077 7341179530369103890599851)
        ·
          refine ⟨11011769295553655835899777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341179530369103890599851 11011769295553655835899777)
          ·
            refine ⟨8258826971665241876924833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11011769295553655835899777 8258826971665241876924833)
            ·
              refine ⟨6194120228748931407693625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8258826971665241876924833 6194120228748931407693625)
              ·
                refine ⟨4645590171561698555770219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194120228748931407693625 4645590171561698555770219)
                ·
                  refine ⟨6968385257342547833655329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645590171561698555770219 6968385257342547833655329)
                  ·
                    refine ⟨5226288943006910875241497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6968385257342547833655329 5226288943006910875241497)
                    ·
                      refine ⟨3919716707255183156431123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226288943006910875241497 3919716707255183156431123)
                      ·
                        rfl

theorem cell23_7633621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7633621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633621 prefixEnd_7633621 := by exact prefixLift 7633621
  have htrace : WordTrace (prefixWord ++ tailWord_7633621) baseStart_7633621 baseEnd_7633621 := by
    simpa [prefixWord, tailWord_7633621, baseEnd_7633621] using wordTrace_append hprefix tailTrace_7633621
  have hstable : (prefixWord ++ tailWord_7633621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633621).length < 2 ^ (prefixWord ++ tailWord_7633621).sum := by decide
  have hdescent : baseEnd_7633621 < baseStart_7633621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633626 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_7633626 : Nat := 118140960795 + 7633626 * 2 ^ 59
def prefixEnd_7633626 : Nat := 4983230072969 + 3 ^ 40 * 7633626 * 2
def baseEnd_7633626 : Nat := 3919719274658455636868599

theorem tailTrace_7633626 : CollatzResearch.WordTrace tailWord_7633626 prefixEnd_7633626 3919719274658455636868599 := by
  unfold tailWord_7633626
  simp only [CollatzResearch.WordTrace]
  refine ⟨69605303360671049092874183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185614142295122797580997821 69605303360671049092874183)
  ·
    refine ⟨104407955041006573639311275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69605303360671049092874183 104407955041006573639311275)
    ·
      refine ⟨156611932561509860458966913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104407955041006573639311275 156611932561509860458966913)
      ·
        refine ⟨117458949421132395344225185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156611932561509860458966913 117458949421132395344225185)
        ·
          refine ⟨88094212065849296508168889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117458949421132395344225185 88094212065849296508168889)
          ·
            refine ⟨66070659049386972381126667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88094212065849296508168889 66070659049386972381126667)
            ·
              refine ⟨99105988574080458571690001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66070659049386972381126667 99105988574080458571690001)
              ·
                refine ⟨74329491430560343928767501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99105988574080458571690001 74329491430560343928767501)
                ·
                  refine ⟨27873559286460128973287813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74329491430560343928767501 27873559286460128973287813)
                  ·
                    refine ⟨5226292366211274182491465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27873559286460128973287813 5226292366211274182491465)
                    ·
                      refine ⟨3919719274658455636868599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226292366211274182491465 3919719274658455636868599)
                      ·
                        rfl

theorem cell23_7633626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_7633626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633626 prefixEnd_7633626 := by exact prefixLift 7633626
  have htrace : WordTrace (prefixWord ++ tailWord_7633626) baseStart_7633626 baseEnd_7633626 := by
    simpa [prefixWord, tailWord_7633626, baseEnd_7633626] using wordTrace_append hprefix tailTrace_7633626
  have hstable : (prefixWord ++ tailWord_7633626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633626).length < 2 ^ (prefixWord ++ tailWord_7633626).sum := by decide
  have hdescent : baseEnd_7633626 < baseStart_7633626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633649 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 7]
def baseStart_7633649 : Nat := 118140960795 + 7633649 * 2 ^ 59
def prefixEnd_7633649 : Nat := 4983230072969 + 3 ^ 40 * 7633649 * 2
def baseEnd_7633649 : Nat := 435525676079278782986777

theorem tailTrace_7633649 : CollatzResearch.WordTrace tailWord_7633649 prefixEnd_7633649 435525676079278782986777 := by
  unfold tailWord_7633649
  simp only [CollatzResearch.WordTrace]
  refine ⟨278422052321600871299584001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185614701547733914199722667 278422052321600871299584001)
  ·
    refine ⟨208816539241200653474688001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278422052321600871299584001 208816539241200653474688001)
    ·
      refine ⟨156612404430900490106016001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208816539241200653474688001 156612404430900490106016001)
      ·
        refine ⟨117459303323175367579512001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156612404430900490106016001 117459303323175367579512001)
        ·
          refine ⟨88094477492381525684634001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117459303323175367579512001 88094477492381525684634001)
          ·
            refine ⟨66070858119286144263475501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88094477492381525684634001 66070858119286144263475501)
            ·
              refine ⟨24776571794732304098803313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66070858119286144263475501 24776571794732304098803313)
              ·
                refine ⟨18582428846049228074102485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24776571794732304098803313 18582428846049228074102485)
                ·
                  refine ⟨435525676079278782986777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18582428846049228074102485 435525676079278782986777)
                  ·
                    rfl

theorem cell23_7633649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_7633649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633649 prefixEnd_7633649 := by exact prefixLift 7633649
  have htrace : WordTrace (prefixWord ++ tailWord_7633649) baseStart_7633649 baseEnd_7633649 := by
    simpa [prefixWord, tailWord_7633649, baseEnd_7633649] using wordTrace_append hprefix tailTrace_7633649
  have hstable : (prefixWord ++ tailWord_7633649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633649).length < 2 ^ (prefixWord ++ tailWord_7633649).sum := by decide
  have hdescent : baseEnd_7633649 < baseStart_7633649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633679 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 4, 5]
def baseStart_7633679 : Nat := 118140960795 + 7633679 * 2 ^ 59
def prefixEnd_7633679 : Nat := 4983230072969 + 3 ^ 40 * 7633679 * 2
def baseEnd_7633679 : Nat := 1306582163044381309835285

theorem tailTrace_7633679 : CollatzResearch.WordTrace tailWord_7633679 prefixEnd_7633679 1306582163044381309835285 := by
  unfold tailWord_7633679
  simp only [CollatzResearch.WordTrace]
  refine ⟨278423146511492186423176091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185615431007661457615450727 278423146511492186423176091)
  ·
    refine ⟨417634719767238279634764137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278423146511492186423176091 417634719767238279634764137)
    ·
      refine ⟨313226039825428709726073103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417634719767238279634764137 313226039825428709726073103)
      ·
        refine ⟨469839059738143064589109655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313226039825428709726073103 469839059738143064589109655)
        ·
          refine ⟨704758589607214596883664483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469839059738143064589109655 704758589607214596883664483)
          ·
            refine ⟨1057137884410821895325496725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704758589607214596883664483 1057137884410821895325496725)
            ·
              refine ⟨49553338331757276343382659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1057137884410821895325496725 49553338331757276343382659)
              ·
                refine ⟨74330007497635914515073989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49553338331757276343382659 74330007497635914515073989)
                ·
                  refine ⟨13936876405806733971576373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74330007497635914515073989 13936876405806733971576373)
                  ·
                    refine ⟨1306582163044381309835285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13936876405806733971576373 1306582163044381309835285)
                    ·
                      rfl

theorem cell23_7633679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_7633679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633679 prefixEnd_7633679 := by exact prefixLift 7633679
  have htrace : WordTrace (prefixWord ++ tailWord_7633679) baseStart_7633679 baseEnd_7633679 := by
    simpa [prefixWord, tailWord_7633679, baseEnd_7633679] using wordTrace_append hprefix tailTrace_7633679
  have hstable : (prefixWord ++ tailWord_7633679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633679).length < 2 ^ (prefixWord ++ tailWord_7633679).sum := by decide
  have hdescent : baseEnd_7633679 < baseStart_7633679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633734 : List Nat := [6, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_7633734 : Nat := 118140960795 + 7633734 * 2 ^ 59
def prefixEnd_7633734 : Nat := 4983230072969 + 3 ^ 40 * 7633734 * 2
def baseEnd_7633734 : Nat := 435530525618793468257567

theorem tailTrace_7633734 : CollatzResearch.WordTrace tailWord_7633734 prefixEnd_7633734 435530525618793468257567 := by
  unfold tailWord_7633734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700786016446654088013383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185616768350861953877618837 8700786016446654088013383)
  ·
    refine ⟨13051179024669981132020075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8700786016446654088013383 13051179024669981132020075)
    ·
      refine ⟨19576768537004971698030113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13051179024669981132020075 19576768537004971698030113)
      ·
        refine ⟨14682576402753728773522585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19576768537004971698030113 14682576402753728773522585)
        ·
          refine ⟨11011932302065296580141939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14682576402753728773522585 11011932302065296580141939)
          ·
            refine ⟨16517898453097944870212909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11011932302065296580141939 16517898453097944870212909)
            ·
              refine ⟨6194211919911729326329841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16517898453097944870212909 6194211919911729326329841)
              ·
                refine ⟨4645658939933796994747381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194211919911729326329841 4645658939933796994747381)
                ·
                  refine ⟨435530525618793468257567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645658939933796994747381 435530525618793468257567)
                  ·
                    rfl

theorem cell23_7633734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_7633734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633734 prefixEnd_7633734 := by exact prefixLift 7633734
  have htrace : WordTrace (prefixWord ++ tailWord_7633734) baseStart_7633734 baseEnd_7633734 := by
    simpa [prefixWord, tailWord_7633734, baseEnd_7633734] using wordTrace_append hprefix tailTrace_7633734
  have hstable : (prefixWord ++ tailWord_7633734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633734).length < 2 ^ (prefixWord ++ tailWord_7633734).sum := by decide
  have hdescent : baseEnd_7633734 < baseStart_7633734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633823 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_7633823 : Nat := 118140960795 + 7633823 * 2 ^ 59
def prefixEnd_7633823 : Nat := 4983230072969 + 3 ^ 40 * 7633823 * 2
def baseEnd_7633823 : Nat := 3919820430347391366105193

theorem tailTrace_7633823 : CollatzResearch.WordTrace tailWord_7633823 prefixEnd_7633823 3919820430347391366105193 := by
  unfold tailWord_7633823
  simp only [CollatzResearch.WordTrace]
  refine ⟨278428398622970499016418123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185618932415313666010945415 278428398622970499016418123)
  ·
    refine ⟨417642597934455748524627185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278428398622970499016418123 417642597934455748524627185)
    ·
      refine ⟨313231948450841811393470389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417642597934455748524627185 313231948450841811393470389)
      ·
        refine ⟨29365495167266419818137849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313231948450841811393470389 29365495167266419818137849)
        ·
          refine ⟨22024121375449814863603387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29365495167266419818137849 22024121375449814863603387)
          ·
            refine ⟨33036182063174722295405081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22024121375449814863603387 33036182063174722295405081)
            ·
              refine ⟨24777136547381041721553811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33036182063174722295405081 24777136547381041721553811)
              ·
                refine ⟨37165704821071562582330717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24777136547381041721553811 37165704821071562582330717)
                ·
                  refine ⟨13937139307901835968374019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37165704821071562582330717 13937139307901835968374019)
                  ·
                    refine ⟨20905708961852753952561029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13937139307901835968374019 20905708961852753952561029)
                    ·
                      refine ⟨3919820430347391366105193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20905708961852753952561029 3919820430347391366105193)
                      ·
                        rfl

theorem cell23_7633823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_7633823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633823 prefixEnd_7633823 := by exact prefixLift 7633823
  have htrace : WordTrace (prefixWord ++ tailWord_7633823) baseStart_7633823 baseEnd_7633823 := by
    simpa [prefixWord, tailWord_7633823, baseEnd_7633823] using wordTrace_append hprefix tailTrace_7633823
  have hstable : (prefixWord ++ tailWord_7633823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633823).length < 2 ^ (prefixWord ++ tailWord_7633823).sum := by decide
  have hdescent : baseEnd_7633823 < baseStart_7633823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633837 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7633837 : Nat := 118140960795 + 7633837 * 2 ^ 59
def prefixEnd_7633837 : Nat := 4983230072969 + 3 ^ 40 * 7633837 * 2
def baseEnd_7633837 : Nat := 1306609206358851437110043

theorem tailTrace_7633837 : CollatzResearch.WordTrace tailWord_7633837 prefixEnd_7633837 1306609206358851437110043 := by
  unfold tailWord_7633837
  simp only [CollatzResearch.WordTrace]
  refine ⟨278428909244919779407427765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185619272829946519604951843 278428909244919779407427765)
  ·
    refine ⟨26102710241711229319446353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278428909244919779407427765 26102710241711229319446353)
    ·
      refine ⟨19577032681283421989584765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26102710241711229319446353 19577032681283421989584765)
      ·
        refine ⟨7341387255481283246094287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19577032681283421989584765 7341387255481283246094287)
        ·
          refine ⟨11012080883221924869141431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341387255481283246094287 11012080883221924869141431)
          ·
            refine ⟨16518121324832887303712147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012080883221924869141431 16518121324832887303712147)
            ·
              refine ⟨24777181987249330955568221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16518121324832887303712147 24777181987249330955568221)
              ·
                refine ⟨9291443245218499108338083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24777181987249330955568221 9291443245218499108338083)
                ·
                  refine ⟨13937164867827748662507125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291443245218499108338083 13937164867827748662507125)
                  ·
                    refine ⟨1306609206358851437110043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13937164867827748662507125 1306609206358851437110043)
                    ·
                      rfl

theorem cell23_7633837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7633837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633837 prefixEnd_7633837 := by exact prefixLift 7633837
  have htrace : WordTrace (prefixWord ++ tailWord_7633837) baseStart_7633837 baseEnd_7633837 := by
    simpa [prefixWord, tailWord_7633837, baseEnd_7633837] using wordTrace_append hprefix tailTrace_7633837
  have hstable : (prefixWord ++ tailWord_7633837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633837).length < 2 ^ (prefixWord ++ tailWord_7633837).sum := by decide
  have hdescent : baseEnd_7633837 < baseStart_7633837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633870 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_7633870 : Nat := 118140960795 + 7633870 * 2 ^ 59
def prefixEnd_7633870 : Nat := 4983230072969 + 3 ^ 40 * 7633870 * 2
def baseEnd_7633870 : Nat := 3919844563938152682217477

theorem tailTrace_7633870 : CollatzResearch.WordTrace tailWord_7633870 prefixEnd_7633870 3919844563938152682217477 := by
  unfold tailWord_7633870
  simp only [CollatzResearch.WordTrace]
  refine ⟨34803764106725028255422383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185620075235866817362252709 34803764106725028255422383)
  ·
    refine ⟨52205646160087542383133575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34803764106725028255422383 52205646160087542383133575)
    ·
      refine ⟨78308469240131313574700363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52205646160087542383133575 78308469240131313574700363)
      ·
        refine ⟨117462703860196970362050545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78308469240131313574700363 117462703860196970362050545)
        ·
          refine ⟨88097027895147727771537909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117462703860196970362050545 88097027895147727771537909)
          ·
            refine ⟨8259096365170099478581679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88097027895147727771537909 8259096365170099478581679)
            ·
              refine ⟨12388644547755149217872519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259096365170099478581679 12388644547755149217872519)
              ·
                refine ⟨18582966821632723826808779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12388644547755149217872519 18582966821632723826808779)
                ·
                  refine ⟨27874450232449085740213169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18582966821632723826808779 27874450232449085740213169)
                  ·
                    refine ⟨20905837674336814305159877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27874450232449085740213169 20905837674336814305159877)
                    ·
                      refine ⟨3919844563938152682217477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20905837674336814305159877 3919844563938152682217477)
                      ·
                        rfl

theorem cell23_7633870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_7633870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633870 prefixEnd_7633870 := by exact prefixLift 7633870
  have htrace : WordTrace (prefixWord ++ tailWord_7633870) baseStart_7633870 baseEnd_7633870 := by
    simpa [prefixWord, tailWord_7633870, baseEnd_7633870] using wordTrace_append hprefix tailTrace_7633870
  have hstable : (prefixWord ++ tailWord_7633870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633870).length < 2 ^ (prefixWord ++ tailWord_7633870).sum := by decide
  have hdescent : baseEnd_7633870 < baseStart_7633870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633877 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7633877 : Nat := 118140960795 + 7633877 * 2 ^ 59
def prefixEnd_7633877 : Nat := 4983230072969 + 3 ^ 40 * 7633877 * 2
def baseEnd_7633877 : Nat := 3919848158302734154829945

theorem tailTrace_7633877 : CollatzResearch.WordTrace tailWord_7633877 prefixEnd_7633877 3919848158302734154829945 := by
  unfold tailWord_7633877
  simp only [CollatzResearch.WordTrace]
  refine ⟨278430368164774866238883885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185620245443183244159255923 278430368164774866238883885)
  ·
    refine ⟨104411388061790574839581457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278430368164774866238883885 104411388061790574839581457)
    ·
      refine ⟨78308541046342931129686093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104411388061790574839581457 78308541046342931129686093)
      ·
        refine ⟨29365702892378599173632285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78308541046342931129686093 29365702892378599173632285)
        ·
          refine ⟨11012138584641974690112107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29365702892378599173632285 11012138584641974690112107)
          ·
            refine ⟨16518207876962962035168161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012138584641974690112107 16518207876962962035168161)
            ·
              refine ⟨12388655907722221526376121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16518207876962962035168161 12388655907722221526376121)
              ·
                refine ⟨9291491930791666144782091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12388655907722221526376121 9291491930791666144782091)
                ·
                  refine ⟨13937237896187499217173137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291491930791666144782091 13937237896187499217173137)
                  ·
                    refine ⟨10452928422140624412879853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13937237896187499217173137 10452928422140624412879853)
                    ·
                      refine ⟨3919848158302734154829945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10452928422140624412879853 3919848158302734154829945)
                      ·
                        rfl

theorem cell23_7633877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7633877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633877 prefixEnd_7633877 := by exact prefixLift 7633877
  have htrace : WordTrace (prefixWord ++ tailWord_7633877) baseStart_7633877 baseEnd_7633877 := by
    simpa [prefixWord, tailWord_7633877, baseEnd_7633877] using wordTrace_append hprefix tailTrace_7633877
  have hstable : (prefixWord ++ tailWord_7633877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633877).length < 2 ^ (prefixWord ++ tailWord_7633877).sum := by decide
  have hdescent : baseEnd_7633877 < baseStart_7633877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633934 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7633934 : Nat := 118140960795 + 7633934 * 2 ^ 59
def prefixEnd_7633934 : Nat := 4983230072969 + 3 ^ 40 * 7633934 * 2
def baseEnd_7633934 : Nat := 3919877426700040431817183

theorem tailTrace_7633934 : CollatzResearch.WordTrace tailWord_7633934 prefixEnd_7633934 3919877426700040431817183 := by
  unfold tailWord_7633934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34804055890696045621713607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185621631417045576649139237 34804055890696045621713607)
  ·
    refine ⟨52206083836044068432570411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34804055890696045621713607 52206083836044068432570411)
    ·
      refine ⟨78309125754066102648855617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52206083836044068432570411 78309125754066102648855617)
      ·
        refine ⟨58731844315549576986641713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78309125754066102648855617 58731844315549576986641713)
        ·
          refine ⟨44048883236662182739981285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58731844315549576986641713 44048883236662182739981285)
          ·
            refine ⟨8259165606874159263746491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44048883236662182739981285 8259165606874159263746491)
            ·
              refine ⟨12388748410311238895619737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8259165606874159263746491 12388748410311238895619737)
              ·
                refine ⟨9291561307733429171714803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12388748410311238895619737 9291561307733429171714803)
                ·
                  refine ⟨13937341961600143757572205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291561307733429171714803 13937341961600143757572205)
                  ·
                    refine ⟨5226503235600053909089577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13937341961600143757572205 5226503235600053909089577)
                    ·
                      refine ⟨3919877426700040431817183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226503235600053909089577 3919877426700040431817183)
                      ·
                        rfl

theorem cell23_7633934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7633934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633934 prefixEnd_7633934 := by exact prefixLift 7633934
  have htrace : WordTrace (prefixWord ++ tailWord_7633934) baseStart_7633934 baseEnd_7633934 := by
    simpa [prefixWord, tailWord_7633934, baseEnd_7633934] using wordTrace_append hprefix tailTrace_7633934
  have hstable : (prefixWord ++ tailWord_7633934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633934).length < 2 ^ (prefixWord ++ tailWord_7633934).sum := by decide
  have hdescent : baseEnd_7633934 < baseStart_7633934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633963 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3]
def baseStart_7633963 : Nat := 118140960795 + 7633963 * 2 ^ 59
def prefixEnd_7633963 : Nat := 4983230072969 + 3 ^ 40 * 7633963 * 2
def baseEnd_7633963 : Nat := 3919892317639020818354549

theorem tailTrace_7633963 : CollatzResearch.WordTrace tailWord_7633963 prefixEnd_7633963 3919892317639020818354549 := by
  unfold tailWord_7633963
  simp only [CollatzResearch.WordTrace]
  refine ⟨278433504842463302926514543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185622336561642201951009695 278433504842463302926514543)
  ·
    refine ⟨417650257263694954389771815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278433504842463302926514543 417650257263694954389771815)
    ·
      refine ⟨626475385895542431584657723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417650257263694954389771815 626475385895542431584657723)
      ·
        refine ⟨939713078843313647376986585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626475385895542431584657723 939713078843313647376986585)
        ·
          refine ⟨704784809132485235532739939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 939713078843313647376986585 704784809132485235532739939)
          ·
            refine ⟨1057177213698727853299109909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704784809132485235532739939 1057177213698727853299109909)
            ·
              refine ⟨49555181892127868123395777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1057177213698727853299109909 49555181892127868123395777)
              ·
                refine ⟨37166386419095901092546833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49555181892127868123395777 37166386419095901092546833)
                ·
                  refine ⟨27874789814321925819410125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37166386419095901092546833 27874789814321925819410125)
                  ·
                    refine ⟨10453046180370722182278797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27874789814321925819410125 10453046180370722182278797)
                    ·
                      refine ⟨3919892317639020818354549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453046180370722182278797 3919892317639020818354549)
                      ·
                        rfl

theorem cell23_7633963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 3].length) (baseStart_7633963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633963 prefixEnd_7633963 := by exact prefixLift 7633963
  have htrace : WordTrace (prefixWord ++ tailWord_7633963) baseStart_7633963 baseEnd_7633963 := by
    simpa [prefixWord, tailWord_7633963, baseEnd_7633963] using wordTrace_append hprefix tailTrace_7633963
  have hstable : (prefixWord ++ tailWord_7633963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633963).length < 2 ^ (prefixWord ++ tailWord_7633963).sum := by decide
  have hdescent : baseEnd_7633963 < baseStart_7633963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633970 : List Nat := [3, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_7633970 : Nat := 118140960795 + 7633970 * 2 ^ 59
def prefixEnd_7633970 : Nat := 4983230072969 + 3 ^ 40 * 7633970 * 2
def baseEnd_7633970 : Nat := 435543990222622476774113

theorem tailTrace_7633970 : CollatzResearch.WordTrace tailWord_7633970 prefixEnd_7633970 435543990222622476774113 := by
  unfold tailWord_7633970
  simp only [CollatzResearch.WordTrace]
  refine ⟨69608440038359485780504841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185622506768958628748012909 69608440038359485780504841)
  ·
    refine ⟨52206330028769614335378631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69608440038359485780504841 52206330028769614335378631)
    ·
      refine ⟨78309495043154421503067947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52206330028769614335378631 78309495043154421503067947)
      ·
        refine ⟨117464242564731632254601921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78309495043154421503067947 117464242564731632254601921)
        ·
          refine ⟨88098181923548724190951441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117464242564731632254601921 88098181923548724190951441)
          ·
            refine ⟨66073636442661543143213581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88098181923548724190951441 66073636442661543143213581)
            ·
              refine ⟨24777613665998078678705093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66073636442661543143213581 24777613665998078678705093)
              ·
                refine ⟨4645802562374639752257205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24777613665998078678705093 4645802562374639752257205)
                ·
                  refine ⟨435543990222622476774113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645802562374639752257205 435543990222622476774113)
                  ·
                    rfl

theorem cell23_7633970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_7633970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633970 prefixEnd_7633970 := by exact prefixLift 7633970
  have htrace : WordTrace (prefixWord ++ tailWord_7633970) baseStart_7633970 baseEnd_7633970 := by
    simpa [prefixWord, tailWord_7633970, baseEnd_7633970] using wordTrace_append hprefix tailTrace_7633970
  have hstable : (prefixWord ++ tailWord_7633970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633970).length < 2 ^ (prefixWord ++ tailWord_7633970).sum := by decide
  have hdescent : baseEnd_7633970 < baseStart_7633970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7633980 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_7633980 : Nat := 118140960795 + 7633980 * 2 ^ 59
def prefixEnd_7633980 : Nat := 4983230072969 + 3 ^ 40 * 7633980 * 2
def baseEnd_7633980 : Nat := 3919901046810147251841971

theorem tailTrace_7633980 : CollatzResearch.WordTrace tailWord_7633980 prefixEnd_7633980 3919901046810147251841971 := by
  unfold tailWord_7633980
  simp only [CollatzResearch.WordTrace]
  refine ⟨139217062441700857414941697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185622749922267809886588929 139217062441700857414941697)
  ·
    refine ⟨104412796831275643061206273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139217062441700857414941697 104412796831275643061206273)
    ·
      refine ⟨78309597623456732295904705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104412796831275643061206273 78309597623456732295904705)
      ·
        refine ⟨58732198217592549221928529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78309597623456732295904705 58732198217592549221928529)
        ·
          refine ⟨44049148663194411916446397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58732198217592549221928529 44049148663194411916446397)
          ·
            refine ⟨16518430748697904468667399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44049148663194411916446397 16518430748697904468667399)
            ·
              refine ⟨24777646123046856703001099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16518430748697904468667399 24777646123046856703001099)
              ·
                refine ⟨37166469184570285054501649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24777646123046856703001099 37166469184570285054501649)
                ·
                  refine ⟨27874851888427713790876237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37166469184570285054501649 27874851888427713790876237)
                  ·
                    refine ⟨10453069458160392671578589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27874851888427713790876237 10453069458160392671578589)
                    ·
                      refine ⟨3919901046810147251841971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453069458160392671578589 3919901046810147251841971)
                      ·
                        rfl

theorem cell23_7633980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_7633980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7633980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7633980 prefixEnd_7633980 := by exact prefixLift 7633980
  have htrace : WordTrace (prefixWord ++ tailWord_7633980) baseStart_7633980 baseEnd_7633980 := by
    simpa [prefixWord, tailWord_7633980, baseEnd_7633980] using wordTrace_append hprefix tailTrace_7633980
  have hstable : (prefixWord ++ tailWord_7633980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7633980).length < 2 ^ (prefixWord ++ tailWord_7633980).sum := by decide
  have hdescent : baseEnd_7633980 < baseStart_7633980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7633980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634014 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_7634014 : Nat := 118140960795 + 7634014 * 2 ^ 59
def prefixEnd_7634014 : Nat := 4983230072969 + 3 ^ 40 * 7634014 * 2
def baseEnd_7634014 : Nat := 3919918505152400118816815

theorem tailTrace_7634014 : CollatzResearch.WordTrace tailWord_7634014 prefixEnd_7634014 3919918505152400118816815 := by
  unfold tailWord_7634014
  simp only [CollatzResearch.WordTrace]
  refine ⟨34804420620659817329577637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185623576643519025757747397 34804420620659817329577637)
  ·
    refine ⟨6525828866373715749295807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34804420620659817329577637 6525828866373715749295807)
    ·
      refine ⟨9788743299560573623943711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525828866373715749295807 9788743299560573623943711)
      ·
        refine ⟨14683114949340860435915567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788743299560573623943711 14683114949340860435915567)
        ·
          refine ⟨22024672424011290653873351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14683114949340860435915567 22024672424011290653873351)
          ·
            refine ⟨33037008636016935980810027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22024672424011290653873351 33037008636016935980810027)
            ·
              refine ⟨49555512954025403971215041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33037008636016935980810027 49555512954025403971215041)
              ·
                refine ⟨37166634715519052978411281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49555512954025403971215041 37166634715519052978411281)
                ·
                  refine ⟨27874976036639289733808461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37166634715519052978411281 27874976036639289733808461)
                  ·
                    refine ⟨10453116013739733650178173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27874976036639289733808461 10453116013739733650178173)
                    ·
                      refine ⟨3919918505152400118816815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453116013739733650178173 3919918505152400118816815)
                      ·
                        rfl

theorem cell23_7634014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_7634014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634014 prefixEnd_7634014 := by exact prefixLift 7634014
  have htrace : WordTrace (prefixWord ++ tailWord_7634014) baseStart_7634014 baseEnd_7634014 := by
    simpa [prefixWord, tailWord_7634014, baseEnd_7634014] using wordTrace_append hprefix tailTrace_7634014
  have hstable : (prefixWord ++ tailWord_7634014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634014).length < 2 ^ (prefixWord ++ tailWord_7634014).sum := by decide
  have hdescent : baseEnd_7634014 < baseStart_7634014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634043 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 6]
def baseStart_7634043 : Nat := 118140960795 + 7634043 * 2 ^ 59
def prefixEnd_7634043 : Nat := 4983230072969 + 3 ^ 40 * 7634043 * 2
def baseEnd_7634043 : Nat := 435548155121264500594909

theorem tailTrace_7634043 : CollatzResearch.WordTrace tailWord_7634043 prefixEnd_7634043 435548155121264500594909 := by
  unfold tailWord_7634043
  simp only [CollatzResearch.WordTrace]
  refine ⟨278436422682173476589426783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185624281788115651059617855 278436422682173476589426783)
  ·
    refine ⟨417654634023260214884140175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278436422682173476589426783 417654634023260214884140175)
    ·
      refine ⟨626481951034890322326210263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417654634023260214884140175 626481951034890322326210263)
      ·
        refine ⟨939722926552335483489315395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626481951034890322326210263 939722926552335483489315395)
        ·
          refine ⟨1409584389828503225233973093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939722926552335483489315395 1409584389828503225233973093)
          ·
            refine ⟨264297073092844354731369955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1409584389828503225233973093 264297073092844354731369955)
            ·
              refine ⟨396445609639266532097054933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264297073092844354731369955 396445609639266532097054933)
              ·
                refine ⟨9291693975920309346024725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396445609639266532097054933 9291693975920309346024725)
                ·
                  refine ⟨435548155121264500594909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9291693975920309346024725 435548155121264500594909)
                  ·
                    rfl

theorem cell23_7634043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 6].length) (baseStart_7634043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634043 prefixEnd_7634043 := by exact prefixLift 7634043
  have htrace : WordTrace (prefixWord ++ tailWord_7634043) baseStart_7634043 baseEnd_7634043 := by
    simpa [prefixWord, tailWord_7634043, baseEnd_7634043] using wordTrace_append hprefix tailTrace_7634043
  have hstable : (prefixWord ++ tailWord_7634043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634043).length < 2 ^ (prefixWord ++ tailWord_7634043).sum := by decide
  have hdescent : baseEnd_7634043 < baseStart_7634043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634073 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_7634073 : Nat := 118140960795 + 7634073 * 2 ^ 59
def prefixEnd_7634073 : Nat := 4983230072969 + 3 ^ 40 * 7634073 * 2
def baseEnd_7634073 : Nat := 1306649600170338462659681

theorem tailTrace_7634073 : CollatzResearch.WordTrace tailWord_7634073 prefixEnd_7634073 1306649600170338462659681 := by
  unfold tailWord_7634073
  simp only [CollatzResearch.WordTrace]
  refine ⟨278437516872064791713018873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185625011248043194475345915 278437516872064791713018873)
  ·
    refine ⟨208828137654048593784764155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278437516872064791713018873 208828137654048593784764155)
    ·
      refine ⟨313242206481072890677146233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208828137654048593784764155 313242206481072890677146233)
      ·
        refine ⟨234931654860804668007859675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313242206481072890677146233 234931654860804668007859675)
        ·
          refine ⟨352397482291207002011789513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234931654860804668007859675 352397482291207002011789513)
          ·
            refine ⟨264298111718405251508842135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352397482291207002011789513 264298111718405251508842135)
            ·
              refine ⟨396447167577607877263263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264298111718405251508842135 396447167577607877263263203)
              ·
                refine ⟨594670751366411815894894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396447167577607877263263203 594670751366411815894894805)
                ·
                  refine ⟨13937595735150276935036597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 594670751366411815894894805 13937595735150276935036597)
                  ·
                    refine ⟨1306649600170338462659681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13937595735150276935036597 1306649600170338462659681)
                    ·
                      rfl

theorem cell23_7634073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_7634073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634073 prefixEnd_7634073 := by exact prefixLift 7634073
  have htrace : WordTrace (prefixWord ++ tailWord_7634073) baseStart_7634073 baseEnd_7634073 := by
    simpa [prefixWord, tailWord_7634073, baseEnd_7634073] using wordTrace_append hprefix tailTrace_7634073
  have hstable : (prefixWord ++ tailWord_7634073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634073).length < 2 ^ (prefixWord ++ tailWord_7634073).sum := by decide
  have hdescent : baseEnd_7634073 < baseStart_7634073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634120 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_7634120 : Nat := 118140960795 + 7634120 * 2 ^ 59
def prefixEnd_7634120 : Nat := 4983230072969 + 3 ^ 40 * 7634120 * 2
def baseEnd_7634120 : Nat := 1306657644700592234697109

theorem tailTrace_7634120 : CollatzResearch.WordTrace tailWord_7634120 prefixEnd_7634120 1306657644700592234697109 := by
  unfold tailWord_7634120
  simp only [CollatzResearch.WordTrace]
  refine ⟨139219615551447259369989907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185626154068596345826653209 139219615551447259369989907)
  ·
    refine ⟨208829423327170889054984861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139219615551447259369989907 208829423327170889054984861)
    ·
      refine ⟨78311033747689083395619323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208829423327170889054984861 78311033747689083395619323)
      ·
        refine ⟨117466550621533625093428985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78311033747689083395619323 117466550621533625093428985)
        ·
          refine ⟨88099912966150218820071739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117466550621533625093428985 88099912966150218820071739)
          ·
            refine ⟨132149869449225328230107609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88099912966150218820071739 132149869449225328230107609)
            ·
              refine ⟨99112402086918996172580707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132149869449225328230107609 99112402086918996172580707)
              ·
                refine ⟨148668603130378494258871061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99112402086918996172580707 148668603130378494258871061)
                ·
                  refine ⟨6968840771736491918384581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148668603130378494258871061 6968840771736491918384581)
                  ·
                    refine ⟨1306657644700592234697109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6968840771736491918384581 1306657644700592234697109)
                    ·
                      rfl

theorem cell23_7634120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_7634120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634120 prefixEnd_7634120 := by exact prefixLift 7634120
  have htrace : WordTrace (prefixWord ++ tailWord_7634120) baseStart_7634120 baseEnd_7634120 := by
    simpa [prefixWord, tailWord_7634120, baseEnd_7634120] using wordTrace_append hprefix tailTrace_7634120
  have hstable : (prefixWord ++ tailWord_7634120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634120).length < 2 ^ (prefixWord ++ tailWord_7634120).sum := by decide
  have hdescent : baseEnd_7634120 < baseStart_7634120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634123 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_7634123 : Nat := 118140960795 + 7634123 * 2 ^ 59
def prefixEnd_7634123 : Nat := 4983230072969 + 3 ^ 40 * 7634123 * 2
def baseEnd_7634123 : Nat := 3919974474543740192353813

theorem tailTrace_7634123 : CollatzResearch.WordTrace tailWord_7634123 prefixEnd_7634123 3919974474543740192353813 := by
  unfold tailWord_7634123
  simp only [CollatzResearch.WordTrace]
  refine ⟨278439340521883650252339023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185626227014589100168226015 278439340521883650252339023)
  ·
    refine ⟨417659010782825475378508535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278439340521883650252339023 417659010782825475378508535)
    ·
      refine ⟨626488516174238213067762803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417659010782825475378508535 626488516174238213067762803)
      ·
        refine ⟨939732774261357319601644205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626488516174238213067762803 939732774261357319601644205)
        ·
          refine ⟨352399790348008994850616577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939732774261357319601644205 352399790348008994850616577)
          ·
            refine ⟨264299842761006746137962433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352399790348008994850616577 264299842761006746137962433)
            ·
              refine ⟨198224882070755059603471825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264299842761006746137962433 198224882070755059603471825)
              ·
                refine ⟨148668661553066294702603869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198224882070755059603471825 148668661553066294702603869)
                ·
                  refine ⟨55750748082399860513476451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148668661553066294702603869 55750748082399860513476451)
                  ·
                    refine ⟨83626122123599790770214677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55750748082399860513476451 83626122123599790770214677)
                    ·
                      refine ⟨3919974474543740192353813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83626122123599790770214677 3919974474543740192353813)
                      ·
                        rfl

theorem cell23_7634123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_7634123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634123 prefixEnd_7634123 := by exact prefixLift 7634123
  have htrace : WordTrace (prefixWord ++ tailWord_7634123) baseStart_7634123 baseEnd_7634123 := by
    simpa [prefixWord, tailWord_7634123, baseEnd_7634123] using wordTrace_append hprefix tailTrace_7634123
  have hstable : (prefixWord ++ tailWord_7634123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634123).length < 2 ^ (prefixWord ++ tailWord_7634123).sum := by decide
  have hdescent : baseEnd_7634123 < baseStart_7634123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634127 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 7, 2, 2]
def baseStart_7634127 : Nat := 118140960795 + 7634127 * 2 ^ 59
def prefixEnd_7634127 : Nat := 4983230072969 + 3 ^ 40 * 7634127 * 2
def baseEnd_7634127 : Nat := 3919976528466358176703795

theorem tailTrace_7634127 : CollatzResearch.WordTrace tailWord_7634127 prefixEnd_7634127 3919976528466358176703795 := by
  unfold tailWord_7634127
  simp only [CollatzResearch.WordTrace]
  refine ⟨278439486413869158935484635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185626324275912772623656423 278439486413869158935484635)
  ·
    refine ⟨417659229620803738403226953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278439486413869158935484635 417659229620803738403226953)
    ·
      refine ⟨313244422215602803802420215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417659229620803738403226953 313244422215602803802420215)
      ·
        refine ⟨469866633323404205703630323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313244422215602803802420215 469866633323404205703630323)
        ·
          refine ⟨704799949985106308555445485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469866633323404205703630323 704799949985106308555445485)
          ·
            refine ⟨264299981244414865708292057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 704799949985106308555445485 264299981244414865708292057)
            ·
              refine ⟨198224985933311149281219043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264299981244414865708292057 198224985933311149281219043)
              ·
                refine ⟨297337478899966723921828565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198224985933311149281219043 297337478899966723921828565)
                ·
                  refine ⟨6968847161717970091917857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297337478899966723921828565 6968847161717970091917857)
                  ·
                    refine ⟨5226635371288477568938393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6968847161717970091917857 5226635371288477568938393)
                    ·
                      refine ⟨3919976528466358176703795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226635371288477568938393 3919976528466358176703795)
                      ·
                        rfl

theorem cell23_7634127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2, 2].length) (baseStart_7634127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634127 prefixEnd_7634127 := by exact prefixLift 7634127
  have htrace : WordTrace (prefixWord ++ tailWord_7634127) baseStart_7634127 baseEnd_7634127 := by
    simpa [prefixWord, tailWord_7634127, baseEnd_7634127] using wordTrace_append hprefix tailTrace_7634127
  have hstable : (prefixWord ++ tailWord_7634127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634127).length < 2 ^ (prefixWord ++ tailWord_7634127).sum := by decide
  have hdescent : baseEnd_7634127 < baseStart_7634127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634157 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7634157 : Nat := 118140960795 + 7634157 * 2 ^ 59
def prefixEnd_7634157 : Nat := 4983230072969 + 3 ^ 40 * 7634157 * 2
def baseEnd_7634157 : Nat := 3919991932885993059328657

theorem tailTrace_7634157 : CollatzResearch.WordTrace tailWord_7634157 prefixEnd_7634157 3919991932885993059328657 := by
  unfold tailWord_7634157
  simp only [CollatzResearch.WordTrace]
  refine ⟨278440580603760474059076725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185627053735840316039384483 278440580603760474059076725)
  ·
    refine ⟨26103804431602544443038443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278440580603760474059076725 26103804431602544443038443)
    ·
      refine ⟨39155706647403816664557665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26103804431602544443038443 39155706647403816664557665)
      ·
        refine ⟨29366779985552862498418249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39155706647403816664557665 29366779985552862498418249)
        ·
          refine ⟨22025084989164646873813687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29366779985552862498418249 22025084989164646873813687)
          ·
            refine ⟨33037627483746970310720531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22025084989164646873813687 33037627483746970310720531)
            ·
              refine ⟨49556441225620455466080797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33037627483746970310720531 49556441225620455466080797)
              ·
                refine ⟨18583665459607670799780299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49556441225620455466080797 18583665459607670799780299)
                ·
                  refine ⟨27875498189411506199670449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18583665459607670799780299 27875498189411506199670449)
                  ·
                    refine ⟨20906623642058629649752837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27875498189411506199670449 20906623642058629649752837)
                    ·
                      refine ⟨3919991932885993059328657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20906623642058629649752837 3919991932885993059328657)
                      ·
                        rfl

theorem cell23_7634157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7634157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634157 prefixEnd_7634157 := by exact prefixLift 7634157
  have htrace : WordTrace (prefixWord ++ tailWord_7634157) baseStart_7634157 baseEnd_7634157 := by
    simpa [prefixWord, tailWord_7634157, baseEnd_7634157] using wordTrace_append hprefix tailTrace_7634157
  have hstable : (prefixWord ++ tailWord_7634157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634157).length < 2 ^ (prefixWord ++ tailWord_7634157).sum := by decide
  have hdescent : baseEnd_7634157 < baseStart_7634157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634177 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_7634177 : Nat := 118140960795 + 7634177 * 2 ^ 59
def prefixEnd_7634177 : Nat := 4983230072969 + 3 ^ 40 * 7634177 * 2
def baseEnd_7634177 : Nat := 3920002202499082981078565

theorem tailTrace_7634177 : CollatzResearch.WordTrace tailWord_7634177 prefixEnd_7634177 3920002202499082981078565 := by
  unfold tailWord_7634177
  simp only [CollatzResearch.WordTrace]
  refine ⟨278441310063688017474804785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185627540042458678316536523 278441310063688017474804785)
  ·
    refine ⟨208830982547766013106103589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278441310063688017474804785 208830982547766013106103589)
    ·
      refine ⟨39155809227706127457394423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208830982547766013106103589 39155809227706127457394423)
      ·
        refine ⟨58733713841559191186091635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39155809227706127457394423 58733713841559191186091635)
        ·
          refine ⟨88100570762338786779137453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58733713841559191186091635 88100570762338786779137453)
          ·
            refine ⟨33037714035877045042176545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88100570762338786779137453 33037714035877045042176545)
            ·
              refine ⟨24778285526907783781632409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33037714035877045042176545 24778285526907783781632409)
              ·
                refine ⟨18583714145180837836224307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24778285526907783781632409 18583714145180837836224307)
                ·
                  refine ⟨27875571217771256754336461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18583714145180837836224307 27875571217771256754336461)
                  ·
                    refine ⟨10453339206664221282876173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27875571217771256754336461 10453339206664221282876173)
                    ·
                      refine ⟨3920002202499082981078565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453339206664221282876173 3920002202499082981078565)
                      ·
                        rfl

theorem cell23_7634177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_7634177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634177 prefixEnd_7634177 := by exact prefixLift 7634177
  have htrace : WordTrace (prefixWord ++ tailWord_7634177) baseStart_7634177 baseEnd_7634177 := by
    simpa [prefixWord, tailWord_7634177, baseEnd_7634177] using wordTrace_append hprefix tailTrace_7634177
  have hstable : (prefixWord ++ tailWord_7634177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634177).length < 2 ^ (prefixWord ++ tailWord_7634177).sum := by decide
  have hdescent : baseEnd_7634177 < baseStart_7634177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634178 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_7634178 : Nat := 118140960795 + 7634178 * 2 ^ 59
def prefixEnd_7634178 : Nat := 4983230072969 + 3 ^ 40 * 7634178 * 2
def baseEnd_7634178 : Nat := 3920002715979737477166061

theorem tailTrace_7634178 : CollatzResearch.WordTrace tailWord_7634178 prefixEnd_7634178 3920002715979737477166061 := by
  unfold tailWord_7634178
  simp only [CollatzResearch.WordTrace]
  refine ⟨69610336634171098661397797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185627564357789596430394125 69610336634171098661397797)
  ·
    refine ⟨13051938118907080999012087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69610336634171098661397797 13051938118907080999012087)
    ·
      refine ⟨19577907178360621498518131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13051938118907080999012087 19577907178360621498518131)
      ·
        refine ⟨29366860767540932247777197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19577907178360621498518131 29366860767540932247777197)
        ·
          refine ⟨11012572787827849592916449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29366860767540932247777197 11012572787827849592916449)
          ·
            refine ⟨8259429590870887194687337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11012572787827849592916449 8259429590870887194687337)
            ·
              refine ⟨6194572193153165396015503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259429590870887194687337 6194572193153165396015503)
              ·
                refine ⟨9291858289729748094023255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194572193153165396015503 9291858289729748094023255)
                ·
                  refine ⟨13937787434594622141034883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9291858289729748094023255 13937787434594622141034883)
                  ·
                    refine ⟨20906681151891933211552325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13937787434594622141034883 20906681151891933211552325)
                    ·
                      refine ⟨3920002715979737477166061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20906681151891933211552325 3920002715979737477166061)
                      ·
                        rfl

theorem cell23_7634178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_7634178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634178 prefixEnd_7634178 := by exact prefixLift 7634178
  have htrace : WordTrace (prefixWord ++ tailWord_7634178) baseStart_7634178 baseEnd_7634178 := by
    simpa [prefixWord, tailWord_7634178, baseEnd_7634178] using wordTrace_append hprefix tailTrace_7634178
  have hstable : (prefixWord ++ tailWord_7634178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634178).length < 2 ^ (prefixWord ++ tailWord_7634178).sum := by decide
  have hdescent : baseEnd_7634178 < baseStart_7634178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634211 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 2, 1, 3]
def baseStart_7634211 : Nat := 118140960795 + 7634211 * 2 ^ 59
def prefixEnd_7634211 : Nat := 4983230072969 + 3 ^ 40 * 7634211 * 2
def baseEnd_7634211 : Nat := 3920019660841335848053409

theorem tailTrace_7634211 : CollatzResearch.WordTrace tailWord_7634211 prefixEnd_7634211 3920019660841335848053409 := by
  unfold tailWord_7634211
  simp only [CollatzResearch.WordTrace]
  refine ⟨278442550145564841281542487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185628366763709894187694991 278442550145564841281542487)
  ·
    refine ⟨417663825218347261922313731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278442550145564841281542487 417663825218347261922313731)
    ·
      refine ⟨626495737827520892883470597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417663825218347261922313731 626495737827520892883470597)
      ·
        refine ⟨117467950842660167415650737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 626495737827520892883470597 117467950842660167415650737)
        ·
          refine ⟨88100963131995125561738053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117467950842660167415650737 88100963131995125561738053)
          ·
            refine ⟨16518930587249086042825885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88100963131995125561738053 16518930587249086042825885)
            ·
              refine ⟨6194598970218407266059707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16518930587249086042825885 6194598970218407266059707)
              ·
                refine ⟨9291898455327610899089561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194598970218407266059707 9291898455327610899089561)
                ·
                  refine ⟨6968923841495708174317171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9291898455327610899089561 6968923841495708174317171)
                  ·
                    refine ⟨10453385762243562261475757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6968923841495708174317171 10453385762243562261475757)
                    ·
                      refine ⟨3920019660841335848053409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453385762243562261475757 3920019660841335848053409)
                      ·
                        rfl

theorem cell23_7634211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_7634211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634211 prefixEnd_7634211 := by exact prefixLift 7634211
  have htrace : WordTrace (prefixWord ++ tailWord_7634211) baseStart_7634211 baseEnd_7634211 := by
    simpa [prefixWord, tailWord_7634211, baseEnd_7634211] using wordTrace_append hprefix tailTrace_7634211
  have hstable : (prefixWord ++ tailWord_7634211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634211).length < 2 ^ (prefixWord ++ tailWord_7634211).sum := by decide
  have hdescent : baseEnd_7634211 < baseStart_7634211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634220 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_7634220 : Nat := 118140960795 + 7634220 * 2 ^ 59
def prefixEnd_7634220 : Nat := 4983230072969 + 3 ^ 40 * 7634220 * 2
def baseEnd_7634220 : Nat := 3920024282167226312840867

theorem tailTrace_7634220 : CollatzResearch.WordTrace tailWord_7634220 prefixEnd_7634220 3920024282167226312840867 := by
  unfold tailWord_7634220
  simp only [CollatzResearch.WordTrace]
  refine ⟨139221439201266117909310057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185628585601688157212413409 139221439201266117909310057)
  ·
    refine ⟨104416079400949588431982543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139221439201266117909310057 104416079400949588431982543)
    ·
      refine ⟨156624119101424382647973815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104416079400949588431982543 156624119101424382647973815)
      ·
        refine ⟨234936178652136573971960723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156624119101424382647973815 234936178652136573971960723)
        ·
          refine ⟨352404267978204860957941085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234936178652136573971960723 352404267978204860957941085)
          ·
            refine ⟨132151600491826822859227907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352404267978204860957941085 132151600491826822859227907)
            ·
              refine ⟨198227400737740234288841861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132151600491826822859227907 198227400737740234288841861)
              ·
                refine ⟨37167637638326293929157849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198227400737740234288841861 37167637638326293929157849)
                ·
                  refine ⟨27875728228744720446868387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37167637638326293929157849 27875728228744720446868387)
                  ·
                    refine ⟨41813592343117080670302581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27875728228744720446868387 41813592343117080670302581)
                    ·
                      refine ⟨3920024282167226312840867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41813592343117080670302581 3920024282167226312840867)
                      ·
                        rfl

theorem cell23_7634220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_7634220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634220 prefixEnd_7634220 := by exact prefixLift 7634220
  have htrace : WordTrace (prefixWord ++ tailWord_7634220) baseStart_7634220 baseEnd_7634220 := by
    simpa [prefixWord, tailWord_7634220, baseEnd_7634220] using wordTrace_append hprefix tailTrace_7634220
  have hstable : (prefixWord ++ tailWord_7634220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634220).length < 2 ^ (prefixWord ++ tailWord_7634220).sum := by decide
  have hdescent : baseEnd_7634220 < baseStart_7634220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634234 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_7634234 : Nat := 118140960795 + 7634234 * 2 ^ 59
def prefixEnd_7634234 : Nat := 4983230072969 + 3 ^ 40 * 7634234 * 2
def baseEnd_7634234 : Nat := 3920031470896389258065803

theorem tailTrace_7634234 : CollatzResearch.WordTrace tailWord_7634234 prefixEnd_7634234 3920031470896389258065803 := by
  unfold tailWord_7634234
  simp only [CollatzResearch.WordTrace]
  refine ⟨69610847256120379052407439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185628926016321010806419837 69610847256120379052407439)
  ·
    refine ⟨104416270884180568578611159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69610847256120379052407439 104416270884180568578611159)
    ·
      refine ⟨156624406326270852867916739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104416270884180568578611159 156624406326270852867916739)
      ·
        refine ⟨234936609489406279301875109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156624406326270852867916739 234936609489406279301875109)
        ·
          refine ⟨44050614279263677369101583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234936609489406279301875109 44050614279263677369101583)
          ·
            refine ⟨66075921418895516053652375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44050614279263677369101583 66075921418895516053652375)
            ·
              refine ⟨99113882128343274080478563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66075921418895516053652375 99113882128343274080478563)
              ·
                refine ⟨148670823192514911120717845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99113882128343274080478563 148670823192514911120717845)
                ·
                  refine ⟨6968944837149136458783649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148670823192514911120717845 6968944837149136458783649)
                  ·
                    refine ⟨5226708627861852344087737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6968944837149136458783649 5226708627861852344087737)
                    ·
                      refine ⟨3920031470896389258065803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226708627861852344087737 3920031470896389258065803)
                      ·
                        rfl

theorem cell23_7634234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_7634234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634234 prefixEnd_7634234 := by exact prefixLift 7634234
  have htrace : WordTrace (prefixWord ++ tailWord_7634234) baseStart_7634234 baseEnd_7634234 := by
    simpa [prefixWord, tailWord_7634234, baseEnd_7634234] using wordTrace_append hprefix tailTrace_7634234
  have hstable : (prefixWord ++ tailWord_7634234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634234).length < 2 ^ (prefixWord ++ tailWord_7634234).sum := by decide
  have hdescent : baseEnd_7634234 < baseStart_7634234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634262 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7634262 : Nat := 118140960795 + 7634262 * 2 ^ 59
def prefixEnd_7634262 : Nat := 4983230072969 + 3 ^ 40 * 7634262 * 2
def baseEnd_7634262 : Nat := 3920045848354715148515675

theorem tailTrace_7634262 : CollatzResearch.WordTrace tailWord_7634262 prefixEnd_7634262 3920045848354715148515675 := by
  unfold tailWord_7634262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402775641773754811978065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185629606845586717994432693 17402775641773754811978065)
  ·
    refine ⟨13052081731330316108983549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17402775641773754811978065 13052081731330316108983549)
    ·
      refine ⟨4894530649248868540868831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13052081731330316108983549 4894530649248868540868831)
      ·
        refine ⟨7341795973873302811303247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894530649248868540868831 7341795973873302811303247)
        ·
          refine ⟨11012693960809954216954871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341795973873302811303247 11012693960809954216954871)
          ·
            refine ⟨16519040941214931325432307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012693960809954216954871 16519040941214931325432307)
            ·
              refine ⟨24778561411822396988148461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16519040941214931325432307 24778561411822396988148461)
              ·
                refine ⟨9291960529433398870555673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24778561411822396988148461 9291960529433398870555673)
                ·
                  refine ⟨6968970397075049152916755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9291960529433398870555673 6968970397075049152916755)
                  ·
                    refine ⟨10453455595612573729375133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6968970397075049152916755 10453455595612573729375133)
                    ·
                      refine ⟨3920045848354715148515675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453455595612573729375133 3920045848354715148515675)
                      ·
                        rfl

theorem cell23_7634262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7634262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634262 prefixEnd_7634262 := by exact prefixLift 7634262
  have htrace : WordTrace (prefixWord ++ tailWord_7634262) baseStart_7634262 baseEnd_7634262 := by
    simpa [prefixWord, tailWord_7634262, baseEnd_7634262] using wordTrace_append hprefix tailTrace_7634262
  have hstable : (prefixWord ++ tailWord_7634262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634262).length < 2 ^ (prefixWord ++ tailWord_7634262).sum := by decide
  have hdescent : baseEnd_7634262 < baseStart_7634262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634287 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 2, 5]
def baseStart_7634287 : Nat := 118140960795 + 7634287 * 2 ^ 59
def prefixEnd_7634287 : Nat := 4983230072969 + 3 ^ 40 * 7634287 * 2
def baseEnd_7634287 : Nat := 1306686228457025850234353

theorem tailTrace_7634287 : CollatzResearch.WordTrace tailWord_7634287 prefixEnd_7634287 1306686228457025850234353 := by
  unfold tailWord_7634287
  simp only [CollatzResearch.WordTrace]
  refine ⟨278445322093289506261309115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185630214728859670840872743 278445322093289506261309115)
  ·
    refine ⟨417667983139934259391963673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278445322093289506261309115 417667983139934259391963673)
    ·
      refine ⟨313250987354950694543972755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417667983139934259391963673 313250987354950694543972755)
      ·
        refine ⟨469876481032426041815959133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313250987354950694543972755 469876481032426041815959133)
        ·
          refine ⟨176203680387159765680984675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469876481032426041815959133 176203680387159765680984675)
          ·
            refine ⟨264305520580739648521477013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176203680387159765680984675 264305520580739648521477013)
            ·
              refine ⟨12389321277222171024444235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 264305520580739648521477013 12389321277222171024444235)
              ·
                refine ⟨18583981915833256536666353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12389321277222171024444235 18583981915833256536666353)
                ·
                  refine ⟨13937986436874942402499765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18583981915833256536666353 13937986436874942402499765)
                  ·
                    refine ⟨1306686228457025850234353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13937986436874942402499765 1306686228457025850234353)
                    ·
                      rfl

theorem cell23_7634287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_7634287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634287 prefixEnd_7634287 := by exact prefixLift 7634287
  have htrace : WordTrace (prefixWord ++ tailWord_7634287) baseStart_7634287 baseEnd_7634287 := by
    simpa [prefixWord, tailWord_7634287, baseEnd_7634287] using wordTrace_append hprefix tailTrace_7634287
  have hstable : (prefixWord ++ tailWord_7634287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634287).length < 2 ^ (prefixWord ++ tailWord_7634287).sum := by decide
  have hdescent : baseEnd_7634287 < baseStart_7634287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634302 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7634302 : Nat := 118140960795 + 7634302 * 2 ^ 59
def prefixEnd_7634302 : Nat := 4983230072969 + 3 ^ 40 * 7634302 * 2
def baseEnd_7634302 : Nat := 3920066387580894992015491

theorem tailTrace_7634302 : CollatzResearch.WordTrace tailWord_7634302 prefixEnd_7634302 3920066387580894992015491 := by
  unfold tailWord_7634302
  simp only [CollatzResearch.WordTrace]
  refine ⟨34805733648529395477888145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185630579458823442548736773 34805733648529395477888145)
  ·
    refine ⟨26104300236397046608416109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34805733648529395477888145 26104300236397046608416109)
    ·
      refine ⟨9789112588648892478156041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26104300236397046608416109 9789112588648892478156041)
      ·
        refine ⟨7341834441486669358617031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9789112588648892478156041 7341834441486669358617031)
        ·
          refine ⟨11012751662230004037925547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341834441486669358617031 11012751662230004037925547)
          ·
            refine ⟨16519127493345006056888321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012751662230004037925547 16519127493345006056888321)
            ·
              refine ⟨12389345620008754542666241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16519127493345006056888321 12389345620008754542666241)
              ·
                refine ⟨9292009215006565906999681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12389345620008754542666241 9292009215006565906999681)
                ·
                  refine ⟨6969006911254924430249761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292009215006565906999681 6969006911254924430249761)
                  ·
                    refine ⟨5226755183441193322687321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6969006911254924430249761 5226755183441193322687321)
                    ·
                      refine ⟨3920066387580894992015491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226755183441193322687321 3920066387580894992015491)
                      ·
                        rfl

theorem cell23_7634302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7634302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634302 prefixEnd_7634302 := by exact prefixLift 7634302
  have htrace : WordTrace (prefixWord ++ tailWord_7634302) baseStart_7634302 baseEnd_7634302 := by
    simpa [prefixWord, tailWord_7634302, baseEnd_7634302] using wordTrace_append hprefix tailTrace_7634302
  have hstable : (prefixWord ++ tailWord_7634302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634302).length < 2 ^ (prefixWord ++ tailWord_7634302).sum := by decide
  have hdescent : baseEnd_7634302 < baseStart_7634302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634327 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_7634327 : Nat := 118140960795 + 7634327 * 2 ^ 59
def prefixEnd_7634327 : Nat := 4983230072969 + 3 ^ 40 * 7634327 * 2
def baseEnd_7634327 : Nat := 3920079224597257394202875

theorem tailTrace_7634327 : CollatzResearch.WordTrace tailWord_7634327 prefixEnd_7634327 3920079224597257394202875 := by
  unfold tailWord_7634327
  simp only [CollatzResearch.WordTrace]
  refine ⟨278446781013144593092765235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185631187342096395395176823 278446781013144593092765235)
  ·
    refine ⟨417670171519716889639147853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278446781013144593092765235 417670171519716889639147853)
    ·
      refine ⟨156626314319893833614680445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 417670171519716889639147853 156626314319893833614680445)
      ·
        refine ⟨58734867869960187605505167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156626314319893833614680445 58734867869960187605505167)
        ·
          refine ⟨88102301804940281408257751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58734867869960187605505167 88102301804940281408257751)
          ·
            refine ⟨132153452707410422112386627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88102301804940281408257751 132153452707410422112386627)
            ·
              refine ⟨198230179061115633168579941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132153452707410422112386627 198230179061115633168579941)
              ·
                refine ⟨37168158573959181219108739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198230179061115633168579941 37168158573959181219108739)
                ·
                  refine ⟨55752237860938771828663109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37168158573959181219108739 55752237860938771828663109)
                  ·
                    refine ⟨10453544598926019717874333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55752237860938771828663109 10453544598926019717874333)
                    ·
                      refine ⟨3920079224597257394202875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10453544598926019717874333 3920079224597257394202875)
                      ·
                        rfl

theorem cell23_7634327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_7634327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634327 prefixEnd_7634327 := by exact prefixLift 7634327
  have htrace : WordTrace (prefixWord ++ tailWord_7634327) baseStart_7634327 baseEnd_7634327 := by
    simpa [prefixWord, tailWord_7634327, baseEnd_7634327] using wordTrace_append hprefix tailTrace_7634327
  have hstable : (prefixWord ++ tailWord_7634327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634327).length < 2 ^ (prefixWord ++ tailWord_7634327).sum := by decide
  have hdescent : baseEnd_7634327 < baseStart_7634327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634364 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 8]
def baseStart_7634364 : Nat := 118140960795 + 7634364 * 2 ^ 59
def prefixEnd_7634364 : Nat := 4983230072969 + 3 ^ 40 * 7634364 * 2
def baseEnd_7634364 : Nat := 435566469264608194382245

theorem tailTrace_7634364 : CollatzResearch.WordTrace tailWord_7634364 prefixEnd_7634364 435566469264608194382245 := by
  unfold tailWord_7634364
  simp only [CollatzResearch.WordTrace]
  refine ⟨139224065257005274205931073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185632087009340365607908097 139224065257005274205931073)
  ·
    refine ⟨104418048942753955654448305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139224065257005274205931073 104418048942753955654448305)
    ·
      refine ⟨78313536707065466740836229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104418048942753955654448305 78313536707065466740836229)
      ·
        refine ⟨14683788132574775013906793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78313536707065466740836229 14683788132574775013906793)
        ·
          refine ⟨11012841099431081260430095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14683788132574775013906793 11012841099431081260430095)
          ·
            refine ⟨16519261649146621890645143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012841099431081260430095 16519261649146621890645143)
            ·
              refine ⟨24778892473719932835967715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16519261649146621890645143 24778892473719932835967715)
              ·
                refine ⟨37168338710579899253951573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24778892473719932835967715 37168338710579899253951573)
                ·
                  refine ⟨435566469264608194382245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37168338710579899253951573 435566469264608194382245)
                  ·
                    rfl

theorem cell23_7634364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_7634364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634364 prefixEnd_7634364 := by exact prefixLift 7634364
  have htrace : WordTrace (prefixWord ++ tailWord_7634364) baseStart_7634364 baseEnd_7634364 := by
    simpa [prefixWord, tailWord_7634364, baseEnd_7634364] using wordTrace_append hprefix tailTrace_7634364
  have hstable : (prefixWord ++ tailWord_7634364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634364).length < 2 ^ (prefixWord ++ tailWord_7634364).sum := by decide
  have hdescent : baseEnd_7634364 < baseStart_7634364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2]
def baseStart_7634384 : Nat := 118140960795 + 7634384 * 2 ^ 59
def prefixEnd_7634384 : Nat := 4983230072969 + 3 ^ 40 * 7634384 * 2
def baseEnd_7634384 : Nat := 3920108492994563671190113

theorem tailTrace_7634384 : CollatzResearch.WordTrace tailWord_7634384 prefixEnd_7634384 3920108492994563671190113 := by
  unfold tailWord_7634384
  simp only [CollatzResearch.WordTrace]
  refine ⟨139224429986969045913795103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185632573315958727885060137 139224429986969045913795103)
  ·
    refine ⟨208836644980453568870692655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139224429986969045913795103 208836644980453568870692655)
    ·
      refine ⟨313254967470680353306038983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208836644980453568870692655 313254967470680353306038983)
      ·
        refine ⟨469882451206020529959058475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313254967470680353306038983 469882451206020529959058475)
        ·
          refine ⟨704823676809030794938587713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469882451206020529959058475 704823676809030794938587713)
          ·
            refine ⟨528617757606773096203940785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704823676809030794938587713 528617757606773096203940785)
            ·
              refine ⟨396463318205079822152955589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528617757606773096203940785 396463318205079822152955589)
              ·
                refine ⟨74336872163452466653679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396463318205079822152955589 74336872163452466653679173)
                ·
                  refine ⟨13938163530647337497564845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74336872163452466653679173 13938163530647337497564845)
                  ·
                    refine ⟨5226811323992751561586817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13938163530647337497564845 5226811323992751561586817)
                    ·
                      refine ⟨3920108492994563671190113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226811323992751561586817 3920108492994563671190113)
                      ·
                        rfl

theorem cell23_7634384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 3, 2].length) (baseStart_7634384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634384 prefixEnd_7634384 := by exact prefixLift 7634384
  have htrace : WordTrace (prefixWord ++ tailWord_7634384) baseStart_7634384 baseEnd_7634384 := by
    simpa [prefixWord, tailWord_7634384, baseEnd_7634384] using wordTrace_append hprefix tailTrace_7634384
  have hstable : (prefixWord ++ tailWord_7634384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634384).length < 2 ^ (prefixWord ++ tailWord_7634384).sum := by decide
  have hdescent : baseEnd_7634384 < baseStart_7634384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634394 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_7634394 : Nat := 118140960795 + 7634394 * 2 ^ 59
def prefixEnd_7634394 : Nat := 4983230072969 + 3 ^ 40 * 7634394 * 2
def baseEnd_7634394 : Nat := 1306704542600369544021689

theorem tailTrace_7634394 : CollatzResearch.WordTrace tailWord_7634394 prefixEnd_7634394 1306704542600369544021689 := by
  unfold tailWord_7634394
  simp only [CollatzResearch.WordTrace]
  refine ⟨69612306175975465883863559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185632816469267909023636157 69612306175975465883863559)
  ·
    refine ⟨104418459263963198825795339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69612306175975465883863559 104418459263963198825795339)
    ·
      refine ⟨156627688895944798238693009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104418459263963198825795339 156627688895944798238693009)
      ·
        refine ⟨117470766671958598679019757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156627688895944798238693009 117470766671958598679019757)
        ·
          refine ⟨44051537501984474504632409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117470766671958598679019757 44051537501984474504632409)
          ·
            refine ⟨33038653126488355878474307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44051537501984474504632409 33038653126488355878474307)
            ·
              refine ⟨49557979689732533817711461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33038653126488355878474307 49557979689732533817711461)
              ·
                refine ⟨9292121191824850090820899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49557979689732533817711461 9292121191824850090820899)
                ·
                  refine ⟨13938181787737275136231349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9292121191824850090820899 13938181787737275136231349)
                  ·
                    refine ⟨1306704542600369544021689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13938181787737275136231349 1306704542600369544021689)
                    ·
                      rfl

theorem cell23_7634394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_7634394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634394 prefixEnd_7634394 := by exact prefixLift 7634394
  have htrace : WordTrace (prefixWord ++ tailWord_7634394) baseStart_7634394 baseEnd_7634394 := by
    simpa [prefixWord, tailWord_7634394, baseEnd_7634394] using wordTrace_append hprefix tailTrace_7634394
  have hstable : (prefixWord ++ tailWord_7634394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634394).length < 2 ^ (prefixWord ++ tailWord_7634394).sum := by decide
  have hdescent : baseEnd_7634394 < baseStart_7634394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634418 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7634418 : Nat := 118140960795 + 7634418 * 2 ^ 59
def prefixEnd_7634418 : Nat := 4983230072969 + 3 ^ 40 * 7634418 * 2
def baseEnd_7634418 : Nat := 3920125951336816538164957

theorem tailTrace_7634418 : CollatzResearch.WordTrace tailWord_7634418 prefixEnd_7634418 3920125951336816538164957 := by
  unfold tailWord_7634418
  simp only [CollatzResearch.WordTrace]
  refine ⟨69612525013953728908581977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185633400037209943756218605 69612525013953728908581977)
  ·
    refine ⟨52209393760465296681436483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69612525013953728908581977 52209393760465296681436483)
    ·
      refine ⟨78314090640697945022154725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52209393760465296681436483 78314090640697945022154725)
      ·
        refine ⟨14683891995130864691654011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78314090640697945022154725 14683891995130864691654011)
        ·
          refine ⟨22025837992696297037481017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14683891995130864691654011 22025837992696297037481017)
          ·
            refine ⟨16519378494522222778110763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22025837992696297037481017 16519378494522222778110763)
            ·
              refine ⟨24779067741783334167166145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16519378494522222778110763 24779067741783334167166145)
              ·
                refine ⟨18584300806337500625374609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24779067741783334167166145 18584300806337500625374609)
                ·
                  refine ⟨13938225604753125469030957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18584300806337500625374609 13938225604753125469030957)
                  ·
                    refine ⟨5226834601782422050886609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13938225604753125469030957 5226834601782422050886609)
                    ·
                      refine ⟨3920125951336816538164957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226834601782422050886609 3920125951336816538164957)
                      ·
                        rfl

theorem cell23_7634418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7634418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634418 prefixEnd_7634418 := by exact prefixLift 7634418
  have htrace : WordTrace (prefixWord ++ tailWord_7634418) baseStart_7634418 baseEnd_7634418 := by
    simpa [prefixWord, tailWord_7634418, baseEnd_7634418] using wordTrace_append hprefix tailTrace_7634418
  have hstable : (prefixWord ++ tailWord_7634418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634418).length < 2 ^ (prefixWord ++ tailWord_7634418).sum := by decide
  have hdescent : baseEnd_7634418 < baseStart_7634418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634424 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_7634424 : Nat := 118140960795 + 7634424 * 2 ^ 59
def prefixEnd_7634424 : Nat := 4983230072969 + 3 ^ 40 * 7634424 * 2
def baseEnd_7634424 : Nat := 1306709677406914504896643

theorem tailTrace_7634424 : CollatzResearch.WordTrace tailWord_7634424 prefixEnd_7634424 1306709677406914504896643 := by
  unfold tailWord_7634424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139225159446896589329523163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185633545929195452439364217 139225159446896589329523163)
  ·
    refine ⟨208837739170344883994284745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139225159446896589329523163 208837739170344883994284745)
    ·
      refine ⟨156628304377758662995713559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208837739170344883994284745 156628304377758662995713559)
      ·
        refine ⟨234942456566637994493570339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156628304377758662995713559 234942456566637994493570339)
        ·
          refine ⟨352413684849956991740355509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234942456566637994493570339 352413684849956991740355509)
          ·
            refine ⟨33038782954683467975658329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352413684849956991740355509 33038782954683467975658329)
            ·
              refine ⟨24779087216012600981743747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33038782954683467975658329 24779087216012600981743747)
              ·
                refine ⟨37168630824018901472615621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24779087216012600981743747 37168630824018901472615621)
                ·
                  refine ⟨6969118279503544026115429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37168630824018901472615621 6969118279503544026115429)
                  ·
                    refine ⟨1306709677406914504896643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969118279503544026115429 1306709677406914504896643)
                    ·
                      rfl

theorem cell23_7634424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_7634424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634424 prefixEnd_7634424 := by exact prefixLift 7634424
  have htrace : WordTrace (prefixWord ++ tailWord_7634424) baseStart_7634424 baseEnd_7634424 := by
    simpa [prefixWord, tailWord_7634424, baseEnd_7634424] using wordTrace_append hprefix tailTrace_7634424
  have hstable : (prefixWord ++ tailWord_7634424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634424).length < 2 ^ (prefixWord ++ tailWord_7634424).sum := by decide
  have hdescent : baseEnd_7634424 < baseStart_7634424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634427 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_7634427 : Nat := 118140960795 + 7634427 * 2 ^ 59
def prefixEnd_7634427 : Nat := 4983230072969 + 3 ^ 40 * 7634427 * 2
def baseEnd_7634427 : Nat := 3920130572662707002952415

theorem tailTrace_7634427 : CollatzResearch.WordTrace tailWord_7634427 prefixEnd_7634427 3920130572662707002952415 := by
  unfold tailWord_7634427
  simp only [CollatzResearch.WordTrace]
  refine ⟨278450428312782310171405535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185633618875188206780937023 278450428312782310171405535)
  ·
    refine ⟨417675642469173465257108303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278450428312782310171405535 417675642469173465257108303)
    ·
      refine ⟨626513463703760197885662455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417675642469173465257108303 626513463703760197885662455)
      ·
        refine ⟨939770195555640296828493683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626513463703760197885662455 939770195555640296828493683)
        ·
          refine ⟨1409655293333460445242740525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939770195555640296828493683 1409655293333460445242740525)
          ·
            refine ⟨528620735000047666966027697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1409655293333460445242740525 528620735000047666966027697)
            ·
              refine ⟨396465551250035750224520773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528620735000047666966027697 396465551250035750224520773)
              ·
                refine ⟨74337290859381703167097645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396465551250035750224520773 74337290859381703167097645)
                ·
                  refine ⟨27876484072268138687661617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74337290859381703167097645 27876484072268138687661617)
                  ·
                    refine ⟨20907363054201104015746213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27876484072268138687661617 20907363054201104015746213)
                    ·
                      refine ⟨3920130572662707002952415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20907363054201104015746213 3920130572662707002952415)
                      ·
                        rfl

theorem cell23_7634427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_7634427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634427 prefixEnd_7634427 := by exact prefixLift 7634427
  have htrace : WordTrace (prefixWord ++ tailWord_7634427) baseStart_7634427 baseEnd_7634427 := by
    simpa [prefixWord, tailWord_7634427, baseEnd_7634427] using wordTrace_append hprefix tailTrace_7634427
  have hstable : (prefixWord ++ tailWord_7634427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634427).length < 2 ^ (prefixWord ++ tailWord_7634427).sum := by decide
  have hdescent : baseEnd_7634427 < baseStart_7634427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7634431 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 3, 2, 2]
def baseStart_7634431 : Nat := 118140960795 + 7634431 * 2 ^ 59
def prefixEnd_7634431 : Nat := 4983230072969 + 3 ^ 40 * 7634431 * 2
def baseEnd_7634431 : Nat := 3920132626585324987302397

theorem tailTrace_7634431 : CollatzResearch.WordTrace tailWord_7634431 prefixEnd_7634431 3920132626585324987302397 := by
  unfold tailWord_7634431
  simp only [CollatzResearch.WordTrace]
  refine ⟨278450574204767818854551147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185633716136511879236367431 278450574204767818854551147)
  ·
    refine ⟨417675861307151728281826721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278450574204767818854551147 417675861307151728281826721)
    ·
      refine ⟨313256895980363796211370041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417675861307151728281826721 313256895980363796211370041)
      ·
        refine ⟨234942671985272847158527531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313256895980363796211370041 234942671985272847158527531)
        ·
          refine ⟨352414007977909270737791297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234942671985272847158527531 352414007977909270737791297)
          ·
            refine ⟨264310505983431953053343473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352414007977909270737791297 264310505983431953053343473)
            ·
              refine ⟨198232879487573964790007605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264310505983431953053343473 198232879487573964790007605)
              ·
                refine ⟨18584332451960059199063213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198232879487573964790007605 18584332451960059199063213)
                ·
                  refine ⟨6969124669485022199648705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18584332451960059199063213 6969124669485022199648705)
                  ·
                    refine ⟨5226843502113766649736529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6969124669485022199648705 5226843502113766649736529)
                    ·
                      refine ⟨3920132626585324987302397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5226843502113766649736529 3920132626585324987302397)
                      ·
                        rfl

theorem cell23_7634431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_7634431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7634431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7634431 prefixEnd_7634431 := by exact prefixLift 7634431
  have htrace : WordTrace (prefixWord ++ tailWord_7634431) baseStart_7634431 baseEnd_7634431 := by
    simpa [prefixWord, tailWord_7634431, baseEnd_7634431] using wordTrace_append hprefix tailTrace_7634431
  have hstable : (prefixWord ++ tailWord_7634431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7634431).length < 2 ^ (prefixWord ++ tailWord_7634431).sum := by decide
  have hdescent : baseEnd_7634431 < baseStart_7634431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7634431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
